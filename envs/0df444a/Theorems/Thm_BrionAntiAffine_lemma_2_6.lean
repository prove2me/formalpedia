-- Prove2me | Theorems.Thm_BrionAntiAffine_lemma_2_6
-- name    : BrionAntiAffine.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:38.574718+00:00
-- url     : https://prove2.me/theorems/771f6f7a-e4f4-46fa-95d7-f4959a046cb7
-- title:
--   Lemma 2.6 — filtration of $\pi_*(\mathcal O_X)$
-- statement:
--   Let $\pi:X\to Y$ be a torsor under a non-trivial connected unipotent algebraic group $U$. Then the quasi-coherent sheaf $\pi_*(\mathcal O_X)$ admits an infinite increasing filtration
--
--   $$0=F_0\subset F_1\subset\cdots\subset\pi_*(\mathcal O_X),\qquad F_{n+1}/F_n\cong\mathcal O_Y,$$
--
--   exhausting $\pi_*(\mathcal O_X)$.
--
--   Proposition 2.5 applies this to the $U$-torsor $G/T\to A$ to compute global sections.
--
--   **Formalization Note** $Y$ is any scheme of finite type over $k$; no quasi-projective or affine hypothesis is imposed.
--
--   Differences from the source:
--   - encoding: a torsor under U → a left action U ⊗ X ⟶ X with (a, pr₂) an isomorphism onto X ×_Y X, π faithfully flat and quasi-compact, all of finite type; reason: a right action becomes a left one through the inverse of U
--   - encoding: unipotent → affine, and every non-zero representation has a non-zero fixed vector; reason: the standard characterization over a field, equivalent to a closed embedding into unitriangular matrices
--   - reading: an infinite increasing filtration, with no starting term or exhaustion stated → F₀ = 0, F_{n+1}/F_n ≅ O_Y for all n, and the F_n exhaust π_*(O_X); reason: the proof builds it from an exhaustive filtration of O(U), and Proposition 2.5 uses exhaustion to compute H⁰; the stronger reading
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Lemma 2.6, p.10

import Mathlib
import Definitions.Def_BrionAntiAffine_IsUnipotent

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Lemma 2.6, Brion, arXiv:0710.5211v3, p.10. Let `π : X → Y` be a torsor under a non-trivial connected
unipotent algebraic group `U`. Then the quasi-coherent sheaf `π_*(𝒪_X)` admits an infinite increasing
filtration with subquotients isomorphic to `𝒪_Y`.

**Formalization Note.** The filtration exhausts `π_*(𝒪_X)`, as the proof of Proposition 2.5, p.10,
uses. `Y` is any `k`-scheme of finite type. -/
theorem lemma_2_6 {U X Y : Sch k} [GrpObj U] (π : X ⟶ Y) (a : U ⊗ X ⟶ X)
    (hU : IsAlgebraicGroup U) (hconn : ConnectedSpace U.left) (hnt : ¬ IsIso (toUnit U))
    (huni : IsUnipotent U) (hπ : IsTorsorUnder π a) :
    ∃ (F : ℕ → Y.left.Modules)
      (incl : ∀ n, F n ⟶ (Scheme.Modules.pushforward π.left).obj (Pic.unitMod X.left))
      (t : ∀ n, F n ⟶ F (n + 1)),
      IsUnitFiltration ((Scheme.Modules.pushforward π.left).obj (Pic.unitMod X.left)) F incl t := by sorry

end BrionAntiAffine
