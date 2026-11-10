-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_proposition_8_1
-- name    : AlgCoverage.OddOrder.proposition_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:47:29.218864+00:00
-- url     : https://prove2.me/theorems/70ff1510-03e4-4c43-8050-d66c37b29b1c
-- title:
--   Proposition 8.1 — finite relative-error bound $|\Pr(H=\varnothing)/e^{-\mu}-1|\le\eta e^{2\mu}+e^{\mu}4^{-R}+4Jm\rho e^{2\mu+\nu}+\beta e^{\mu+\nu}$
-- statement:
--   Let $G$ be a finite group of odd order $N$ with a supplied series (6.1) ($J$ layers, $D=\max d_r$), $X\in G^k$ iid uniform inputs, $M=2^k-1$, and $B\subseteq G\setminus\{1_G\}$ deterministic with $m=|B|\ge1$. Let $R\ge2$ and $T=R+1\le M/8$, suppose both local suffix blocks of (8.2) have positive length ($\ell_1=\lfloor k/128\rfloor\ge1$, $\ell_2=\lfloor k/64\rfloor-\ell_1\ge1$), and assume $\mu=mM/N\le R/(4e)$. Choose the envelopes $(B_*,A_*)$ from (5.9), and define $\rho=B_*2^{n_2}(31/32)^{n_1}$, $\nu=m2^k/N$ by (8.2), $\beta=\min\{1,JA_*(2^{-\ell_1}+2^{-\ell_2})\}$ by (7.5), and $\eta=\max_{0\le i\le R}\{4i^2/M+2\beta+4J(m+1)\rho4^i\}$. Then
--   $$\Big|\frac{\Pr(H=\varnothing)}{e^{-\mu}}-1\Big|\le\eta e^{2\mu}+e^{\mu}4^{-R}+4Jm\rho e^{2\mu+\nu}+\beta e^{\mu+\nu}. \tag{8.8}$$
--   Here $H=\varnothing$ is the event that no nonempty word hits $B$, i.e. $B\cap\mathcal W_k=\varnothing$. Both envelope choices of (5.9) are asserted: $(B(T,D),A(T,D))$ for every series, and $(B_{\rm sc}(T),A_{\rm sc}(T))$ when every layer has dimension one (the series (5.8)). This finite certificate is what Theorem 3.1 is derived from.
--
--   Differences from the source:
--   - encoding: a supplied G-normal elementary-abelian series (6.1) and FULL as surjectivity of the coefficient map at every layer → s : NormalEASeries G (0-based layers A (r+1)/A r, every layer nontrivial: d_r ≥ 1) and FULL s x U: every target in A_{r+1}^j is hit modulo A_r by the layer word ∏ P_i a_i P_i⁻¹ for some lifts a ∈ A_{r+1}^k; reason: the layer quotient is abelian and normal in G/A_r, so this is surjectivity of the induced linear coefficient map with coefficients θ(prefix) of form (5.1); d_r ≥ 1 is the reading of (6.1) declared in eq_6_1 (J ≤ log₃ N needs it), and a series with trivial layers collapses to one without them with the same FULL and no larger J
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
--   - reading: 'Choose the envelopes from (5.9)' → two conjuncts: the general envelopes (B(T,D), A(T,D)) for every series, and the scalar envelopes (B_sc(T), A_sc(T)) when every layer has dimension one; reason: (5.9) offers both routes and the paper applies the bound with each
--   - encoding: T = R + 1 ≤ M/8 and µ ≤ R/(4e) → real inequalities (R + 1 : ℝ) ≤ (2^k − 1)/8 and paramMu ≤ R/(4·exp 1); reason: same conditions
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 26 (PDF 27), Proposition 8.1, Eq. (8.8); p. 24 (PDF 25), Eq. (8.2)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage
import Definitions.Def_AlgCoverage_OddOrder_CommonStream
import Definitions.Def_AlgCoverage_OddOrder_Series
import Definitions.Def_AlgCoverage_OddOrder_TwoBlock
import Definitions.Def_AlgCoverage_OddOrder_Sieve

namespace AlgCoverage.OddOrder

/-- Proposition 8.1 (finite relative-error bound), Lin, printed p. 26 / PDF 27. `G` of odd order `N`
with a supplied series (6.1) (`J` layers, `D = max d_r`), iid inputs `X ∈ G^k`, a deterministic
nonidentity target set `B` with `m = |B| ≥ 1`, `M = 2^k − 1`, `R ≥ 2`, `T = R + 1 ≤ M/8`, both local
suffix blocks of (8.2) of positive length (`ℓ₁ = ⌊k/128⌋ ≥ 1`, `ℓ₂ = ⌊k/64⌋ − ℓ₁ ≥ 1`), and
`µ = mM/N ≤ R/(4e)`. With envelopes `(B_*, A_*)` from (5.9), `ρ = B_* 2^{n₂}(31/32)^{n₁}`,
`ν = m2^k/N`, `β = min{1, J A_*(2^{−ℓ₁} + 2^{−ℓ₂})}` and
`η = max_{0≤i≤R} {4i²/M + 2β + 4J(m+1)ρ4^i}`:
`|Pr(H = ∅)/e^{−µ} − 1| ≤ η e^{2µ} + e^µ 4^{−R} + 4Jmρ e^{2µ+ν} + β e^{µ+ν}` (8.8).
Both envelope choices of (5.9) are asserted: the general `(B(T,D), A(T,D))` for every series, and the
scalar `(B_sc(T), A_sc(T))` when every layer has dimension one (the series (5.8)). -/
theorem proposition_8_1 (G : Type*) [Group G] [Fintype G] (hodd : Odd (Fintype.card G))
    (s : NormalEASeries G) (k R : ℕ) (B : Finset G) (hB : (1 : G) ∉ B) (hm : 1 ≤ B.card)
    (hR : 2 ≤ R) (hT : ((R + 1 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ k - 1) / 8)
    (hl₁ : 1 ≤ paramL1 k) (hl₂ : 1 ≤ paramL2 k)
    (hmu : paramMu B.card k (Fintype.card G) ≤ (R : ℝ) / (4 * Real.exp 1)) :
    |probIid G k (fun x => activeSet B x = ∅) /
          Real.exp (-paramMu B.card k (Fintype.card G)) - 1| ≤
        paramEta R k s.J B.card (betaDef s.J (envA (R + 1) s.D) (paramL1 k) (paramL2 k))
            (paramRho (envB (R + 1) s.D) k) *
            Real.exp (2 * paramMu B.card k (Fintype.card G)) +
          Real.exp (paramMu B.card k (Fintype.card G)) * (4 : ℝ) ^ (-(R : ℤ)) +
          4 * (s.J : ℝ) * B.card * paramRho (envB (R + 1) s.D) k *
            Real.exp (2 * paramMu B.card k (Fintype.card G) + paramNu B.card k (Fintype.card G)) +
          betaDef s.J (envA (R + 1) s.D) (paramL1 k) (paramL2 k) *
            Real.exp (paramMu B.card k (Fintype.card G) + paramNu B.card k (Fintype.card G)) ∧
    ((∀ r, r < s.J → s.d r = 1) →
      |probIid G k (fun x => activeSet B x = ∅) /
            Real.exp (-paramMu B.card k (Fintype.card G)) - 1| ≤
          paramEta R k s.J B.card (betaDef s.J (envAsc (R + 1)) (paramL1 k) (paramL2 k))
              (paramRho (envBsc (R + 1)) k) *
              Real.exp (2 * paramMu B.card k (Fintype.card G)) +
            Real.exp (paramMu B.card k (Fintype.card G)) * (4 : ℝ) ^ (-(R : ℤ)) +
            4 * (s.J : ℝ) * B.card * paramRho (envBsc (R + 1)) k *
              Real.exp (2 * paramMu B.card k (Fintype.card G) + paramNu B.card k (Fintype.card G)) +
            betaDef s.J (envAsc (R + 1)) (paramL1 k) (paramL2 k) *
              Real.exp (paramMu B.card k (Fintype.card G) + paramNu B.card k (Fintype.card G))) := by sorry

end AlgCoverage.OddOrder
