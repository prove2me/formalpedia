-- Prove2me | Theorems.Thm_AlgebraicCurve_cartier_map_eq_map_cartier_of_constantFieldExtension
-- name    : AlgebraicCurve.cartier_map_eq_map_cartier_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/353129fd-a636-5bd7-a89a-67b40da3d755
-- title:
--   Cartier operator commutes with constant-field base change
-- statement:
--   Let $K, F, K', F'$ be fields with $F$ a $K$-algebra, $F'$ a $K'$-algebra, and compatible algebra structures $K \to K'$, $F \to F'$, $K \to F'$ forming scalar towers $K \to K' \to F'$ and $K \to F \to F'$ with commuting $K'$- and $F$-actions on $F'$. Assume $K$ is perfect and that $F$ is a curve over $K$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor $D$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ and $\deg D = 0$, each place (a proper valuation subring of $F$ containing the image of $K$ whose ring is a principal ideal ring) has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Let $p$ be a prime with $\mathrm{char}\,K = p$, and assume there is $x \in F$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$. Let $C$ be an additive endomorphism of $\Omega_{F/K}$ satisfying Cartier's three laws $C(f^p\omega) = fC(\omega)$, $C(df) = 0$, $C(f^{p-1}df) = df$, and let $C'$ be an additive endomorphism of $\Omega_{F'/K'}$ satisfying the same three laws over $K'$. Then $C'(\mathrm{map}(\omega)) = \mathrm{map}(C(\omega))$ for every $\omega \in \Omega_{F/K}$, where $\mathrm{map}$ is the canonical map $\Omega_{F/K} \to \Omega_{F'/K'}$.
--
--   This is the functoriality of the Cartier operator under an arbitrary compatible extension of the constant field, in particular under a constant-field extension $F' = K'\cdot F$. It is used in the construction of a Cartier-fixed regular differential after passage to an algebraically closed constant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_cartier_map_eq_map_cartier_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.cartier_map_eq_map_cartier_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [PerfectField K] [AlgebraicCurve.IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (C' : Ω[F'⁄K'] →+ Ω[F'⁄K'])
    (hsemi' : ∀ (f : F') (ω : Ω[F'⁄K']), C' (f ^ p • ω) = f • C' ω)
    (hker' : ∀ f : F', C' (KaehlerDifferential.D K' F' f) = 0)
    (hlog' : ∀ f : F', C' (f ^ (p - 1) • KaehlerDifferential.D K' F' f) = KaehlerDifferential.D K' F' f) :
    ∀ ω : Ω[F⁄K], C' (KaehlerDifferential.map K K' F F' ω) = KaehlerDifferential.map K K' F F' (C ω) := by sorry
