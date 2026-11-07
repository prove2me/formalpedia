-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_7_5
-- name    : ArbSlowFP.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:01.963544+00:00
-- url     : https://prove2.me/theorems/1eeaaa31-af08-4297-911d-288db33ccfa0
-- title:
--   Lemma 7.5 — reset action bounds uniform in $T_2$ (56), (57)
-- statement:
--   Let an order-$k$ clock carry the additional data of Definition 6.2 and fix $\mathcal R$. As $T_1\to\infty$, uniformly over integers $T_2\ge\max\{T_1,\upsilon_k\}$,
--   $$C_\times=\kappa\mathbf 1_r\mathbf 1_r^\top+O(T_1^{-2}),\quad Q=P_0^\top X+O(T_1^{-1}),\quad P=P_0+O(T_1^{-1}).$$
--   Consequently there is an integer $T_0$ depending only on the parent data such that for every integer $T_1\ge T_0$ and every integer $T_2\ge\max\{T_1,\upsilon_k\}$:
--
--   1. $0<c<1$, and $\gamma=M_{:,k}>0$ entrywise;
--   2. every entry of $J$ strictly below the diagonal is positive: $C_\times>0$ entrywise and $\eta>0$;
--   3. the early columns of $P$ are strictly negative and its late columns strictly positive;
--   4. with $a_{\min}=\min_{0\le i\le g}a_i>0$ and $\epsilon=a_{\min}/4$: $-P_{ij}>\epsilon$ for parent actions $i$ and $0\le j<r$, and $-P_{gj}-c>A_k$ for $0\le j<r$.
--
--   The statement also includes the exact output of the construction at these parameters (p.52): $PM=D$, $P^\top X=Q$, $M^\top JM=E$, the closed-form inverses $(53)$, and $GC_+=R_+N$.
--
--   Differences from the source:
--   - encoding: O(·) as T₁ → ∞ with parent data fixed → explicit constants K, T₀ quantified before T₁ and T₂, with the norm (45) written as two inequalities; reason: this is the definition of O printed on p.49
--   - encoding: T₀ "depending only on the parent data" → K, T₀ quantified after the fixed section R; reason: p.49 fixes R, which depends only on k, before T₁
--   - generalization: the conclusions of the lemma → together with PM = D, P⊤X = Q, M⊤JM = E, (53), (40) and GC₊ = R₊N in one predicate ResetBoundsAt; reason: these are established on pp.51–52 and p.56 for the same parameters, and later statements use them at the same T₁, T₂; the printed lemma is the part without these clauses
--   - encoding: a rational linear map R : im(L) → ℚ^{w×w} with L(R(F)) = F, fixed before T₁ → any ℚ-linear map Rmap on all w×w matrices with L(Rmap F) = F for F ∈ im L (IsSection), quantified before T₀; reason: every linear map on im L extends to the whole space and every such map restricts to one; Rmap is only evaluated on im L at the T₁ ≥ T₀ the statement covers
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.52, Lemma 7.5; exact output on pp.51–52

import Mathlib
import Definitions.Def_ArbSlowFP_LiftParams

open Matrix

namespace ArbSlowFP

/-- Lemma 7.5, p.52 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). For an order-k
clock with the additional data of Definition 6.2 and a fixed section `R` of `L`, as `T₁ → ∞`, uniformly over
integers `T₂ ≥ max{T₁, υ_k}`: `C× = κ11⊤ + O(T₁⁻²)`, `Q = P₀⊤X + O(T₁⁻¹)`, `P = P₀ + O(T₁⁻¹)` (56); and there
is an integer `T₀` depending only on the parent data such that for all such `T₁ ≥ T₀`, `T₂`: (i) `0 < c < 1`,
`γ = M_{:,k} > 0`; (ii) every entry of `J` strictly below the diagonal is positive (`C× > 0`, `η > 0`);
(iii) `P_E < 0 < P_L`; (iv) the margins (57).

**Formalization Note.** `O` is written out with constants `K`, `T₀` depending only on the parent data
(and on the fixed section `R`) in the norm (45), matching p.49. The clauses `PM = D`, `P⊤X = Q`, `M⊤JM = E`,
`GC₊ = R₊N` and the inverses (53) established on pp.51–52 are the construction's exact output, and they are
part of `ResetBoundsAt`. -/
theorem lemma_7_5 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (τ : ℕ) (cref : ℚ) (ℓs : Fin (k + 1) → ℚ) (aP : ι → ℚ)
    (ha : IsAddData d.parent (d.Ak + 3) τ cref ℓs aP)
    (Rmap : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hR : IsSection Rmap) :
    let L := d.liftParams τ cref ℓs aP Rmap
    ∃ (K : ℚ) (T0 : ℕ), 1 ≤ T0 ∧ ∀ T1 T2 : ℕ, T0 ≤ T1 → L.IsAdmissible T1 T2 →
      NormStarLE (L.Cx T1 T2 - Matrix.of fun _ _ => L.kappa T1) (K / (T1 : ℚ) ^ 2) ∧
      NormStarLE (L.Q T1 T2 - L.P0ᵀ * L.P.X τ) (K / (T1 : ℚ)) ∧
      NormStarLE (L.Pc T1 T2 - L.P0) (K / (T1 : ℚ)) ∧
      L.ResetBoundsAt T1 T2 := by sorry

end ArbSlowFP
