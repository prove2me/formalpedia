-- Prove2me | Theorems.Thm_BlockBochner_theorem_3
-- name    : BlockBochner.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:13.351429+00:00
-- url     : https://prove2.me/theorems/ed7612d8-d0ba-4134-99ee-d351f2c61563
-- title:
--   Theorem 3 — block Glauber dynamics has spectral gap at least $(1-\lambda_{\max}(H))/m$
-- statement:
--   Let $\mu$ be a probability measure on the configurations $\prod_{v\in V}S_v$ of a spin system with finitely many sites and standard Borel spin spaces, such that $\ker L_{\mathrm{Glaub}}$ consists only of constant functions (connectedness). Let $A=(a_{uv})$ be a symmetric $V\times V$ matrix with non-negative entries, zero diagonal and $\lambda_{\max}(A)<1$, and $M=I-A$. For disjoint sets of sites $T_1,\dots,T_m\subseteq V$ with $T=\bigsqcup_aT_a\ne\emptyset$ define
--   $$C=((M^{-1})_T)^{-1},\qquad D=\mathrm{blockdiag}(C_{T_1},\dots,C_{T_m}),\qquad H=I-D^{-1/2}CD^{-1/2}.$$
--   If for all $u\ne v$ in $V$ and almost all pinnings $\tau$ of $V\setminus\{u,v\}$
--   $$\lambda_2(L^\tau_{\mathrm{Glaub}})\ge\frac{1-a_{uv}}2,$$
--   then
--   $$\lambda_2\bigl(L^{T_1,\dots,T_m}_{\mathrm{Glaub}}\bigr)\ge\frac{1-\lambda_{\max}(H)}m .$$
--
--   With singleton blocks covering $V$ one has $C=I-A$, $D=I$, $H=A$, and the theorem gives the local-to-global bound $\lambda_2(L_{\mathrm{Glaub}})\ge(1-\lambda_{\max}(A))/|V|$.
--
--   **Formalization Note** $\lambda_2(L)\ge\gamma$ is the predicate `GapAtLeast`. The link $\mu^\tau$ is a regular conditional distribution and the hypothesis is required for almost every pinning with respect to the law of the pinned spins. Individual blocks may be empty, as in the source; the factor $1/m$ counts all $m$ blocks.
--
--   Differences from the source:
--   - encoding: a spin system on a graph G = (V, E), its configurations distributed by µ → a probability measure µ on ∏_v S_v, no graph; reason: G only restricts which configurations µ charges; every probability measure on the product is the measure of a spin system (E = ∅), so the instances are the same
--   - encoding: λ₂(L) ≥ γ → GapAtLeast L γ: γ⟨f, Lf⟩ ≤ ‖Lf‖² for all f and dim ker L ≤ 1 (Module.rank); reason: the Sec. 1.1 definition of λ₂, for γ > 0 (here γ = (1 − a_uv)/2 > 0 and (1 − λ_max(H))/m > 0)
--   - encoding: all pinnings τ of V ∖ {u, v} → pinLaw µ {u, v}-a.e. τ, with µ^τ = condDistrib; reason: the source states that all statements about pinnings hold a.e. w.r.t. the law of the pinned spins (Sec. 2.2, p.15); conditional laws are defined only up to null sets
--   - encoding: disjoint subsets T₁, …, T_m ⊂ V → T : Fin m → Finset V pairwise disjoint, with T = ⋃ T_a nonempty; reason: λ_max(H) is undefined for the empty matrix; ⊂ is read as ⊆
--   - encoding: spin spaces S_v → standard Borel and nonempty; reason: standard Borel is the setting of Sec. 2.2, p.15; nonemptiness follows from µ being a probability measure on the product
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 3, p.4 (proof Sec. 3.4, p.26)

import Mathlib
import Definitions.Def_BlockBochner_GapAtLeast
import Definitions.Def_BlockBochner_IsConnectedGlauber
import Definitions.Def_BlockBochner_IsAdmissible
import Definitions.Def_BlockBochner_blockLap
import Definitions.Def_BlockBochner_pinLaw
import Definitions.Def_BlockBochner_linkLaw
import Definitions.Def_BlockBochner_lamMax
import Definitions.Def_BlockBochner_matH

open MeasureTheory

namespace BlockBochner

/-- **Theorem 3 (block Glauber dynamics).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 3, p.4 (proof Sec. 3.4, p.26).

Let `µ` be a probability measure on `∏_{v∈V} S_v` (finitely many sites, standard Borel spin spaces)
whose Glauber Laplacian has only constants in its kernel. Let `A` be a symmetric `V × V` matrix with
non-negative entries, zero diagonal and `λ_max(A) < 1`, `M = I − A`, and let `T₁, …, T_m` be disjoint
sets of sites with `T = ⊔_a T_a`; put `C = ((M⁻¹)_T)⁻¹`, `D = blockdiag(C_{T₁}, …, C_{T_m})`,
`H = I − D^{−1/2} C D^{−1/2}`. If for all `u ≠ v` and (almost) all pinnings `τ` of `V ∖ {u, v}`,
`λ₂(L^τ_Glaub) ≥ (1 − a_{uv})/2`, then `λ₂(L^{T₁,…,T_m}_Glaub) ≥ (1 − λ_max(H))/m`.

**Formalization Note** `λ₂(L) ≥ γ` is `GapAtLeast L γ`. Pinnings are regular conditional
distributions (`linkLaw`) and the hypothesis holds for `pinLaw µ {u, v}`-a.e. `τ` (Sec. 2.2, p.15).
The graph `G` only shapes `µ` and is omitted. `T` is assumed nonempty, so that `H` is a nonempty
matrix; individual blocks may be empty, as in the source. -/
theorem theorem_3 {V : Type*} [Fintype V] [DecidableEq V] {S : V → Type*}
    [∀ v, MeasurableSpace (S v)] [∀ v, StandardBorelSpace (S v)] [∀ v, Nonempty (S v)]
    (μ : Measure (∀ v, S v)) [IsProbabilityMeasure μ] (hconn : IsConnectedGlauber μ)
    (A : Matrix V V ℝ) (hA : IsAdmissible A)
    {m : ℕ} (T : Fin m → Finset V) (hT : Pairwise fun a b => Disjoint (T a) (T b))
    (hTne : (blockUnion T).Nonempty)
    (hlink : ∀ u v, u ≠ v → ∀ᵐ τ ∂(pinLaw μ {u, v}),
      GapAtLeast (glauberLap (linkLaw μ {u, v} τ)) ((1 - A u v) / 2)) :
    GapAtLeast (blockLap μ T) ((1 - lamMax (matH A T)) / m) := by sorry

end BlockBochner
