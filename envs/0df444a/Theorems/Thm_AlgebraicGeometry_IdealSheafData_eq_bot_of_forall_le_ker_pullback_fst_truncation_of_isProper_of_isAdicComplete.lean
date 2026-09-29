-- Prove2me | Theorems.Thm_AlgebraicGeometry_IdealSheafData_eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.IdealSheafData.eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/59c1f462-c152-581d-9475-82dff5792f86
-- title:
--   An ideal sheaf killed by all truncations vanishes
-- statement:
--   Let $R$ be a commutative Noetherian ring, $I \subseteq R$ an ideal, and suppose $R$ is $I$-adically complete. Let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a proper morphism. Let $(s_n)_{n \in \mathbb{N}}$ be a family of morphisms $s_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$, assumed to be given by the spectra of the quotient maps, i.e. $s_n$ is the morphism induced by the structure map $R \to R/I^{n+1}$ for every $n$. Let $J$ be an ideal sheaf on $X$ (a term of `X.IdealSheafData`), and assume that for every $n$ one has $J \le (\text{pullback.fst } f\ s_n).\mathrm{ker}$, the kernel ideal sheaf on $X$ of the first projection $X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1}) \to X$. The conclusion is that $J = \bot$, the zero ideal sheaf. The family $(s_n)$ is passed as data together with the equations pinning it down, rather than being formed inside the statement.
--
--   This is the statement that the closed subschemes $X \times_R \operatorname{Spec}(R/I^{n+1})$ are jointly scheme-theoretically dense in a proper $\operatorname{Spec} R$-scheme when $R$ is Noetherian and $I$-adically complete; it rests on Krull's intersection theorem together with the fact that $I$ lies in the Jacobson radical of $R$. It is the separation input for the formal-GAGA style comparison results: it is used to prove uniqueness of morphisms agreeing on all truncations, and that a finite morphism which is a closed immersion (resp. an isomorphism) after every truncation is one already.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IdealSheafData_eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IdealSheafData.eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (J : X.IdealSheafData) (hJ : ∀ n : ℕ, J ≤ (Limits.pullback.fst f (sR n)).ker) :
    J = ⊥ := by sorry
