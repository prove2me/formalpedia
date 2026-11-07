-- Prove2me | Theorems.Thm_CritWinSpin_theorem_6_3
-- name    : CritWinSpin.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:46:08.625696+00:00
-- url     : https://prove2.me/theorems/8cf9f50a-fbe7-48bc-8816-4238e9b18c26
-- title:
--   Theorem 6.3, pp.24–25 — the lifted model in the critical window and $\hat L_{T,k}$ with error $CTe^{-n^2}$
-- statement:
--   Fix $\rho$ GHS of type $p$, $w\ge1$, $\varepsilon\in(0,d_p)$, integers $A,C$ as in (36). For all large $n$ and every rational $H$ on $\{\pm1\}^n$ with $(J_0)_{ii}=0$ and $W=\mathrm{wd}(J_0,h_0)\le n^w$:
--
--   1. a polynomial-time computation gives a rational model $(\tilde J,\tilde h)$ on $A^N$, $N=n^{1+pC}$, with
--   $$0\preceq\tilde J\preceq\tau(1+N^{-d_p+\varepsilon})I_N,\qquad\mathrm{wd}(\tilde J,\tilde h)\le C_\rho,$$
--   and $\tilde h=0$ whenever $h_0=0$;
--   2. there is $C_{\mathrm{cap}}>0$ depending only on $\rho$ such that for every $k\ge1$, $T\ge\lceil C_{\mathrm{cap}}(k+n^2)\rceil$, the procedure $\hat L_{T,k}$ runs in time $\mathrm{poly}(N,T)$, satisfies $Y(X_j)=F_{i_j}$ whenever it does not fail, and
--   $$\mathrm{TV}(\hat L_{T,k}(\mu_H^{\otimes T}),\pi^{\otimes k})\le CTe^{-n^2}.$$
--
--   This places the lifted hard instances inside the critical window and converts source samples into Gibbs samples.
--
--   Differences from the source:
--   - generalization: H of bit complexity poly(n) → no bound on the bit length of H; the machines run in time polynomial in their input; reason: with bit complexity poly(n) this is poly(n), as printed
--   - generalization: û dyadic → the spectral, width and sampling claims for every rational û with (28); the computed û is any such; reason: (28) is all that the proof uses
--   - reading: the procedure runs in time poly(N, T), with Step 1 at finite precision → ∃ PPT slot machine with TV to the ideal step ≤ e^{−2n²} at every input; the running time of L̂_{T,k} is T times the slot time; reason: the printed error per step and the fact that L̂ is T independent slots; the precision scheme [Bre76, SL25] is not pinned
--   - reading: C in (37), C_ρ in (i) → C, C_ρ, C_cap after ρ and p, before w, ε, A, C; the threshold on n after them; reason: §3, p.10: constants depend only on ρ
--   - encoding: the procedure stops at the k-th acceptance → all T slots drawn; the first k accepted are kept; reason: same output law, since the slots are independent
--   - encoding: (J̃, h̃) in (ii) and N = n^{1+pC} → the product index [n] × [r] in (ii), and [N] with N = n · n^{pC} in (i), reindexed by finProdFinEquiv; reason: the same model
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 6.3, pp.24–25, eq. (37); procedure, p.24; eq. (36), p.24

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- **Theorem 6.3, gadget reduction** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…,
pp.24–25). Fix `ρ` of type `p`, `w ≥ 1`, `ε ∈ (0, d_p)` and integers `A, C` as in (36). For all large `n` and
every rational symmetric zero-diagonal `H` on `{±1}^n` with `wd(J₀, h₀) ≤ n^w`:
(i) the lift of (30), (36) on `N = nr` sites has `0 ⪯ J̃ ⪯ τ(1 + N^{−d_p+ε}) I_N` and `wd(J̃, h̃) ≤ C_ρ`, with
`h̃ = 0` when `h₀ = 0`, and a polynomial-time map computes it together with some `û` satisfying (28);
(ii) a PPT slot machine, within `e^{−2n²}` of the ideal rejection step in total variation at every input,
makes `L̂_{T,k}` satisfy `Y(X_j) = F_{i_j}` whenever it does not fail and, for `k ≥ 1`,
`T ≥ ⌈C_cap(k + n²)⌉`, `TV(L̂_{T,k}(μ_H^{⊗T}), π^{⊗k}) ≤ C T e^{−n²}`, eq. (37).

**Formalization Note.** `C_ρ`, `C_cap` and `C` depend only on `ρ` (§3, p.10); the threshold on `n` depends
also on `w, ε, A, C`. The running time of `L̂_{T,k}` is `T` times that of the slot machine. -/
theorem theorem_6_3 (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ Cρ Ccap Cv : ℝ, 0 < Cρ ∧ 0 < Ccap ∧ 0 < Cv ∧
      ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
        ∃ (liftF : Str → Str) (slotM : PPT) (n₀ : ℕ), CookPvsNP.PolyTimeComputable liftF ∧
          ∀ (n : ℕ) (H : Inst n), n₀ ≤ n → H.1.IsSymm → (∀ i, H.1 i i = 0) →
            width (castM H.1) (castV H.2) ≤ (n : ℝ) ^ w →
            -- (i), for every admissible `û`
            (∀ û : ℚ, IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û →
              (castM (liftInst S p Ac Cc H û).1).PosSemidef ∧
              ((tau S * (1 + ((n * cloudSize p Cc n : ℕ) : ℝ) ^ (-dExp p + ε))) •
                  (1 : Matrix (Fin (n * cloudSize p Cc n)) (Fin (n * cloudSize p Cc n)) ℝ) -
                castM (liftInst S p Ac Cc H û).1).PosSemidef ∧
              width (castM (liftInst S p Ac Cc H û).1) (castV (liftInst S p Ac Cc H û).2) ≤ Cρ ∧
              (H.2 = 0 → (liftInst S p Ac Cc H û).2 = 0)) ∧
            -- (i), the polynomial-time computation
            (∃ û : ℚ, IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û ∧
              liftF (encInst H) = tupleCode [encInst (liftInst S p Ac Cc H û), encRat û]) ∧
            -- (ii)
            (∀ û : ℚ, IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û →
              (∀ y : BinCfg n,
                tvDist (slotKernel S p Cc slotM H û y)
                    (idealSlot S (((tauQ S + thetaQ p Ac Cc n : ℚ) : ℝ)) (castM H.1) (castV H.2)
                      (û : ℝ) y) ≤
                  Real.exp (-(2 * (n : ℝ) ^ 2))) ∧
              LhatDecodes (slotKernel S p Cc slotM H û) ∧
              ∀ k T : ℕ, 1 ≤ k → ⌈Ccap * ((k : ℝ) + (n : ℝ) ^ 2)⌉₊ ≤ T →
                tvDist (LhatMu (slotKernel S p Cc slotM H û) (muH (castM H.1) (castV H.2)) T k)
                    (gibbsTupleOpt S (castM (liftJQ S p Ac Cc H û)) (castV (liftHQ p Cc H û)) k) ≤
                  Cv * (T : ℝ) * Real.exp (-((n : ℝ) ^ 2))) := by sorry

end CritWinSpin
