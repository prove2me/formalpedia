-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_section_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_section_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/846ea51a-8d8a-5602-8c11-c85d0186ca90
-- title:
--   Equality of two sections spreads out to a finitely generated stage
-- statement:
--   Let $a,b$ be rationals, $\Lambda$ a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ and $N$ a natural number. Let $L$ be a commutative ring and $R \subseteq L$ a $\mathbb Z$-subalgebra which is finitely generated (as a $\mathbb Z$-algebra), and let $E_R$ be a `FakeEllipticCurve` for the data $(\Lambda, N)$ over $R$; this consists of a scheme $A$ with a morphism $f : A \to \operatorname{Spec} R$ carrying a commutative relative group law, an `AbelianSchemePropertyBundle` for $f$ (so $f$ is smooth, proper, with connected fibres and admitting a relative group law), all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $\operatorname{Spec} R$ which is additive and multiplicative in the appropriate sense and satisfies the trace condition on tangent spaces at geometric points, together with further curve data. Let $\sigma_1,\sigma_2$ be two sections of $f$, i.e. morphisms $\operatorname{Spec} R \to A$ whose composite with $f$ is the identity of $\operatorname{Spec} R$, and assume that $\sigma_1$ and $\sigma_2$ become equal after base change along the inclusion $R \hookrightarrow L$, that is, the morphism $\operatorname{Spec} L \to \operatorname{Spec} R$ followed by $\sigma_1$ equals the same morphism followed by $\sigma_2$. Then for every finite subset $s$ of $L$ there is a finitely generated $\mathbb Z$-subalgebra $R'$ of $L$ with $R \le R'$ and $s \subseteq R'$ such that the morphism $\operatorname{Spec} R' \to \operatorname{Spec} R$ induced by the inclusion $R \hookrightarrow R'$, followed by $\sigma_1$, equals the same morphism followed by $\sigma_2$.
--
--   This is the spreading-out principle that equality of two morphisms from a quasi-compact scheme into a scheme locally of finite type over the base descends from a limit ring to a finite stage (EGA IV₃ 8.8.2.4), specialised to two sections of a fake elliptic curve and re-indexed by finitely generated $\mathbb Z$-subalgebras of $L$ containing $R$. It is used in the construction of full level structures on fake elliptic curves over finitely generated subalgebras, where a pullback/level condition verified over $L$ must be realised over one such stage.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_section_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_section_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (L : Type) [CommRing L] (R : Subalgebra ℤ L) (hR : R.FG) (ER : FakeEllipticCurve Λ N ↥R)
    (σ₁ σ₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R))) ER.f)
    (h : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ σ₁.1 = Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ σ₂.1)
    (s : Finset L) :
    ∃ (R' : Subalgebra ℤ L) (_ : R'.FG) (hRR' : R ≤ R') (_ : (↑s : Set L) ⊆ R'),
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom) ≫ σ₁.1 =
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom) ≫ σ₂.1 := by sorry
