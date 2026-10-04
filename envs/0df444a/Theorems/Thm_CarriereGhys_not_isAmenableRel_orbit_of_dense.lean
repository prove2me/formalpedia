-- Prove2me | Theorems.Thm_CarriereGhys_not_isAmenableRel_orbit_of_dense
-- name    : CarriereGhys.not_isAmenableRel_orbit_of_dense
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:56:47.717594+00:00
-- url     : https://prove2.me/theorems/39166fa9-7fa4-49ca-9b6e-58c78cd87b8c
-- title:
--   Carrière–Ghys — the orbit relation of a countable dense subgroup of PSL₂(ℝ) on P¹ is not amenable
-- statement:
--   Let $\Gamma$ be a countable dense subgroup of $\mathrm{PSL}_2(\mathbb R)$. Then the orbit relation of $\Gamma$ on the projective line $\mathbf P^1 = \mathbb R \cup \{\infty\}$, the set of pairs $(x, \gamma x)$ with $\gamma \in \Gamma$ acting by Möbius transformations, is not amenable with respect to Lebesgue measure.
--
--   Here $\mathrm{PSL}_2(\mathbb R)$ is `Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)`, the quotient of $\mathrm{SL}_2(\mathbb R)$ by its centre $\{\pm 1\}$, with the quotient topology; the orbit relation is written through matrices $A \in \mathrm{SL}_2(\mathbb R)$ whose class lies in $\Gamma$, acting by `Monod.mob`. Lebesgue measure on $\mathbf P^1$ is `Monod.volP1`, and amenability is `Monod.IsAmenableRel` from the Monod bundle: the existence of a left invariant mean on the relation, in the sense of the bundle's definition.
--
--   Lodha and Moore state it as Theorem 2.2 (p. 4): "If $\Gamma$ is a countable dense subgroup of $\mathrm{PSL}_2(\mathbb R)$, then the action of $\Gamma$ on the real projective line induces an orbit equivalence relation which is not amenable with respect to Lebesgue measure", citing Carrière and Ghys (1985). The published `Monod.not_isAmenableRel_mob` is the case $\Gamma = \mathrm{PSL}_2(A)$ for a countable dense subring $A$ of $\mathbb R$; a countable dense subgroup need contain no such group (a dense free subgroup contains no $\mathrm{PSL}_2(A)$, since $\mathrm{PSL}_2(A) \supseteq \mathrm{PSL}_2(\mathbb Z)$ has torsion).
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 4, Theorem 2.2, which cites Carrière, Y. and Ghys, É., Relations d'équivalence moyennables sur les groupes de Lie, C. R. Acad. Sci. Paris Sér. I Math. 300 (1985), no. 19, 677–680 (no DOI)

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace CarriereGhys

theorem not_isAmenableRel_orbit_of_dense
    (Γ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ))) [Countable Γ]
    (hΓ : Dense (Γ : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)))) :
    ¬ Monod.IsAmenableRel Monod.volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ A : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
        (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) ∈ Γ ∧
          Monod.mob A p.1 = p.2} := by
  sorry

end CarriereGhys
