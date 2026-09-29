-- Prove2me | Theorems.Thm_ArtinL_Abelian_induced_apply_isConj_eq_nPlus_sub_nMinus
-- name    : ArtinL.Abelian.induced_apply_isConj_eq_nPlus_sub_nMinus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/cb981afc-1fc8-5974-be53-66abb4508042
-- title:
--   Induced character at complex conjugation equals n₊-n₋
-- statement:
--   Let $F$ be a number field of characteristic-zero field type which is Galois over $\mathbb{Q}$, let $\varphi\colon F\to\mathbb{C}$ be a ring homomorphism and let $\sigma\in G:=\mathrm{Gal}(F/\mathbb{Q})$ satisfy `ComplexEmbedding.IsConj φ σ`, i.e. $\sigma$ is the complex conjugation attached to $\varphi$, so that $\overline{\varphi(x)}=\varphi(\sigma x)$ for all $x\in F$. Let $H\le G$ be a subgroup and $\chi\colon H\to\mathbb{C}^{\times}$ a group homomorphism. Write $K=F^{H}$ for the fixed field of $H$ and let $\psi=$ [`ArtinL.Abelian.ofSubgroup H χ`](def/ArtinL_Abelian.html#L94) be the character of $\mathrm{Gal}(F/K)$ obtained from $\chi$ by transporting along the canonical isomorphism $\mathrm{Gal}(F/K)\cong\mathrm{Fix}(K)=H$. Then
--   $$\frac{1}{|H|}\sum_{x\in G}\ \bigl[\,x^{-1}\sigma x\in H\,\bigr]\ \chi(x^{-1}\sigma x)\;=\;n_{+}(\psi)-n_{-}(\psi),$$
--   the sum being over all of $G$ with the summand taken to be $0$ when $x^{-1}\sigma x\notin H$. Here $n_{+}(\psi)$ is the number of infinite places $v$ of $K$ that are real and satisfy: for every infinite place $w$ of $F$ restricting to $v$, $\psi$ is trivial on the stabiliser of $w$ in $\mathrm{Gal}(F/K)$; and $n_{-}(\psi)$ is the truncated difference $r_1(K)-n_{+}(\psi)$, where $r_1(K)$ is the number of real places of $K$.
--
--   This is the classical evaluation of the induced character $\mathrm{Ind}_{H}^{G}\chi$ at a complex conjugation $\sigma$: the left-hand side is the induced-character formula, and the right-hand side counts the real places of $K=F^{H}$ at which $\chi$ is trivial on the local decomposition group minus those at which it is not. It is used in the determination of the archimedean factors, and hence of the sign conditions in the functional equation, by [`ArtinL.exists_completedLSeries_functionalEquation_of_odd`](thm.html#ArtinL.exists_completedLSeries_functionalEquation_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_induced_apply_isConj_eq_nPlus_sub_nMinus.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

universe u

open scoped Classical in

theorem ArtinL.Abelian.induced_apply_isConj_eq_nPlus_sub_nMinus
    {F : Type u} [Field F] [NumberField F] [IsGalois ℚ F]
    (φ : F →+* ℂ) (σ : F ≃ₐ[ℚ] F) (hσ : ComplexEmbedding.IsConj φ σ)
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) :
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F, (if hx : x⁻¹ * σ * x ∈ H then (((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ)) else 0) =
      (ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup H χ) : ℂ) -
        ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup H χ) := by sorry
