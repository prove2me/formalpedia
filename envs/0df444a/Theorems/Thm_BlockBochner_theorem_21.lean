-- Prove2me | Theorems.Thm_BlockBochner_theorem_21
-- name    : BlockBochner.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:38:14.360424+00:00
-- url     : https://prove2.me/theorems/a980395b-3191-4d14-90a9-0197946376b9
-- title:
--   Theorem 21 — $\|\tilde Pf\|^2\le\alpha^{-1}\sum_a\|\tilde Q_af\|^2$
-- statement:
--   Let $H$ be a real Hilbert space, $W_1,\dots,W_n$ closed subspaces with orthogonal projections $P_i$, $P_{ij}$ the projection onto $W_i\cap W_j$, and $S=(s_{ij})$ a real symmetric matrix with non-negative entries, zero diagonal and $\lambda_{\max}(S)<1$ such that $\|P_iP_j-P_{ij}\|\le s_{ij}$ for all $i\ne j$. Let $M=I-S$ and let $B$ be the Bochner operator on $H_1=\bigoplus_iW_i$.
--   Let $T_1,\dots,T_m\subseteq[n]$ be disjoint nonempty subsets and $T=\bigsqcup_aT_a$. Let $H_T=\bigcap_{i\notin T}W_i^\perp$, $\tilde W_i=H_T\cap(H_T\cap W_i^\perp)^\perp$, $\tilde Q_a$ the orthogonal projection onto $\sum_{i\in T_a}\tilde W_i$ and $\tilde P$ the orthogonal projection onto $\sum_{i\in T}\tilde W_i$. Define $C=((M^{-1})_T)^{-1}$, $D=\mathrm{blockdiag}(C_{T_1},\dots,C_{T_m})$ and $\alpha=\lambda_{\min}(D^{-1/2}CD^{-1/2})$. Then
--   $$\|\tilde Pf\|^2\le\alpha^{-1}\sum_{a=1}^m\|\tilde Q_af\|^2\qquad\text{for all }f\in H_T .$$
--
--   This is the Hilbert-space core of Theorem 3: with $H=L^2(\mu)$ and $W_i=\operatorname{ran}L_i$ it becomes a Poincaré inequality for the block dynamics.
--
--   **Formalization Note** The projections onto $\sum\tilde W_i$ are onto its closure and are taken in $H$; since $\tilde W_i\subseteq H_T$ they agree on $H_T$ with the projections $H_T\to H_T$ of the source.
--
--   Differences from the source:
--   - encoding: orthogonal projections H_T → H_T onto Σ W̃_i → projections in H onto the closure of Σ W̃_i (projCl); reason: for f ∈ H_T they coincide, since the subspaces lie in H_T; a projection onto a non-closed sum is onto its closure
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 21, p.22 (setting Sec. 3.2, p.21)

import Mathlib
import Definitions.Def_BlockBochner_Wt
import Definitions.Def_BlockBochner_projCl
import Definitions.Def_BlockBochner_IsAdmissible
import Definitions.Def_BlockBochner_lamMin
import Definitions.Def_BlockBochner_matD
import Definitions.Def_BlockBochner_invSqrt

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Theorem 21.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 21, p.22 (setting Sec. 3.2, p.21). Suppose `‖P_iP_j − P_{ij}‖ ≤ s_{ij}`
for all `i ≠ j`, for a real symmetric matrix `S` with non-negative entries, zero diagonal and maximum
eigenvalue strictly less than `1`. Let `M = I − S`, `C = ((M⁻¹)_T)⁻¹`,
`D = blockdiag(C_{T₁}, …, C_{T_m})` and `α = λ_min(D^{−1/2} C D^{−1/2})`. Then
`‖P̃f‖² ≤ α⁻¹ Σ_{a=1}^m ‖Q̃_a f‖²` for all `f ∈ H_T`.

Here `T₁, …, T_m ⊂ [n]` are disjoint nonempty subsets, `T = ⊔_a T_a`, `H_T = ∩_{i∉T} W_i^⊥`,
`W̃_i = H_T ∩ (H_T ∩ W_i^⊥)^⊥`, `Q̃_a` is the orthogonal projection onto `Σ_{i∈T_a} W̃_i` and `P̃` the
orthogonal projection onto `Σ_{i∈T} W̃_i`.

**Formalization Note** The projections onto `Σ W̃_i` are onto the closure (`projCl`) and are taken in
`H`; since `W̃_i ⊆ H_T`, on `f ∈ H_T` they agree with the projections `H_T → H_T` of the source. -/
theorem theorem_21 {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsAdmissible S)
    (hang : ∀ i j, i ≠ j → ‖(W i : Submodule ℝ H).starProjection ∘L (W j : Submodule ℝ H).starProjection -
      ((W i ⊓ W j : ClosedSubmodule ℝ H) : Submodule ℝ H).starProjection‖ ≤ S i j)
    {m : ℕ} (T : Fin m → Finset (Fin n)) (hT : Pairwise fun a b => Disjoint (T a) (T b))
    (hTne : ∀ a, (T a).Nonempty) (f : H) (hf : f ∈ HT W (blockUnion T)) :
    ‖projCl (⨆ i ∈ blockUnion T, Wt W (blockUnion T) i) f‖ ^ 2 ≤
      (lamMin (invSqrt (matD S T) * matC S T * invSqrt (matD S T)))⁻¹ *
        ∑ a, ‖projCl (⨆ i ∈ T a, Wt W (blockUnion T) i) f‖ ^ 2 := by sorry

end BlockBochner
