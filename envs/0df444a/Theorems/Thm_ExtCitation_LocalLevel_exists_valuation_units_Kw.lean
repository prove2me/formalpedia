-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_exists_valuation_units_Kw
-- name    : ExtCitation.LocalLevel.exists_valuation_units_Kw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/e06563b3-b779-5102-bd33-6912604fc043
-- title:
--   Normalised discrete valuation on a finite extension K_w/ℚ_q
-- statement:
--   Let $q$ be a prime and let $K_w$ be an intermediate field of the extension $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}}_q$ (the algebraic closure `PadicAlgCl q`) which is finite-dimensional over $\mathbb{Q}_q$; write $R_w =$ `Rw q Kw` for the valuation subring of $K_w$ obtained by pulling back along $K_w \hookrightarrow \overline{\mathbb{Q}}_q$ the valuation subring of the canonical $\mathbb{R}_{\ge 0}$-valued valuation on $\overline{\mathbb{Q}}_q$. The assertion is that there exists a monoid homomorphism $v : K_w^{\times} \to \mathrm{Multiplicative}\,\mathbb{Z}$ with four properties: $v$ is surjective; for every unit $x$ of $K_w$ one has $v(x) = 1$ precisely when both $x$ and $x^{-1}$, viewed as elements of $K_w$, lie in $R_w$ (so the kernel of $v$ is exactly the unit group of $R_w$, expressed without unit-group coercions); $v$ is invariant under the Galois action, i.e. $v(\sigma x) = v(x)$ for every $\mathbb{Q}_q$-algebra automorphism $\sigma$ of $K_w$ and every $x \in K_w^{\times}$, where $\sigma$ acts through the induced map on units; and $v$ is normalised with the multiplicative order reversed relative to divisibility, in that $v(x) \le 1$ whenever $x \in R_w$ (additively, elements of $R_w$ have non-positive valuation, so a uniformiser is sent to a negative generator).
--
--   This is the existence of the normalised discrete valuation $K_w^{\times} \twoheadrightarrow \mathbb{Z}$ attached to the ring of integers $R_w$ of a finite extension of $\mathbb{Q}_q$, together with the exactness datum $1 \to R_w^{\times} \to K_w^{\times} \to \mathbb{Z} \to 0$ and its Galois equivariance; it rests on the fact that $R_w$ is a discrete valuation ring ([`ExtCitation.LocalLevel.isDiscreteValuationRing_Rw`](thm.html#ExtCitation.LocalLevel.isDiscreteValuationRing_Rw)). It is used in the local computations at $w$ — ranks of invariants in $K_w^{\times}/(K_w^{\times})^n$, orders of cohomology groups of unit groups, and norm-index bookkeeping — that feed the local conditions in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_exists_valuation_units_Kw.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.exists_valuation_units_Kw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    ∃ v : (↥Kw)ˣ →* Multiplicative ℤ, Function.Surjective v ∧
      (∀ x : (↥Kw)ˣ, v x = 1 ↔ ((x : Kw) ∈ Rw q Kw ∧ ((x⁻¹ : (↥Kw)ˣ) : Kw) ∈ Rw q Kw)) ∧
      (∀ (σ : Kw ≃ₐ[ℚ_[q]] Kw) (x : (↥Kw)ˣ), v (Units.map (σ : Kw →* Kw) x) = v x) ∧
      (∀ x : (↥Kw)ˣ, (x : Kw) ∈ Rw q Kw → v x ≤ 1) := by sorry
