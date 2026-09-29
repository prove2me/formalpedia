-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed
-- name    : AlgebraicCurve.exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/69419117-4b86-52cb-84a3-ba1c8522593a
-- title:
--   Cartier-fixed regular differentials and algebraically closed constant-field extensions
-- statement:
--   Let $K \subseteq K'$ and $F \subseteq F'$ be fields forming a commutative square of algebras ($K$-algebra $F$, $K'$-algebra $F'$, together with $K \to K'$, $F \to F'$ and $K \to F'$, the two scalar towers $K \to K' \to F'$ and $K \to F \to F'$, and commuting $K'$- and $F$-actions on $F'$), with $K$ and $K'$ algebraically closed and $F$, $F'$ essentially of finite type over $K$, $K'$ respectively. Assume $F/K$ and $F'/K'$ are curves in the sense of the project: all divisors of nonzero functions exist and have degree $0$, every place (a proper valuation subring containing the image of the base field, whose maximal ideal is principal) has residue field finite over the base field, and the module of Kähler differentials is free of rank one over the function field. Let $p$ be a prime with $\operatorname{char} K = p$. Assume $F$ contains an element transcendental over $K$ over which $F$ is finite, likewise $F'$ over $K'$, and that $K'$ adjoined to the image of $F$ in $F'$ is all of $F'$. Let $C \colon \Omega_{F/K} \to \Omega_{F/K}$ and $C' \colon \Omega_{F'/K'} \to \Omega_{F'/K'}$ be additive maps satisfying the Cartier laws $C(f^p\omega) = f\,C\omega$, $C(\mathrm{d}f) = 0$ and $C(f^{p-1}\mathrm{d}f) = \mathrm{d}f$, and the same for $C'$. Then every $\omega'$ which is regular (for each place $w$ of $F'/K'$, $\omega' = f \cdot \mathrm{d}(\text{uniformiser of } w)$ for some $f$ in the valuation subring of $w$) and satisfies $C'\omega' = \omega'$ is of the form $\omega' = \mathrm{map}(\omega)$ for some regular $\omega \in \Omega_{F/K}$ with $C\omega = \omega$, where $\mathrm{map}$ is the base-change map $\Omega_{F/K} \to \Omega_{F'/K'}$.
--
--   This is the statement that the $\mathbb{F}_p$-space of Cartier-fixed (logarithmic) regular differentials, whose dimension is the $p$-rank or Hasse–Witt invariant of the curve, does not grow under an extension of algebraically closed constant fields; equivalently, no new $p$-torsion points of the Jacobian appear. It is used in the analysis of $q$-expansions on modular curves, through [`ModularCurve.exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord`](thm.html#ModularCurve.exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [IsAlgClosed K] [IsAlgClosed K'] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K' F']
    [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K' F']
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (C' : Ω[F'⁄K'] →+ Ω[F'⁄K'])
    (hsemi' : ∀ (f : F') (ω : Ω[F'⁄K']), C' (f ^ p • ω) = f • C' ω)
    (hker' : ∀ f : F', C' (KaehlerDifferential.D K' F' f) = 0)
    (hlog' : ∀ f : F', C' (f ^ (p - 1) • KaehlerDifferential.D K' F' f) = KaehlerDifferential.D K' F' f) :
    ∀ ω' ∈ AlgebraicCurve.regularDifferentials K' F', C' ω' = ω' →
      ∃ ω ∈ AlgebraicCurve.regularDifferentials K F, C ω = ω ∧ KaehlerDifferential.map K K' F F' ω = ω' := by sorry
