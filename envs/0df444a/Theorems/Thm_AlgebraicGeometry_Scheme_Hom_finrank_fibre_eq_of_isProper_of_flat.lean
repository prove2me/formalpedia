-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_fibre_eq_of_isProper_of_flat
-- name    : AlgebraicGeometry.Scheme.Hom.finrank_fibre_eq_of_isProper_of_flat
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:51:42.716804+00:00
-- url     : https://prove2.me/theorems/918a7698-6d25-4170-96b4-34e6f16365bc
-- title:
--   Conservation of number for proper morphisms: over an irreducible locally noetherian base, finite fibres along which the morphism is flat all have the same degree
-- statement:
--   Let $p : Z \to T$ be a proper morphism of schemes, where $T$ is locally noetherian and irreducible. Let $t_0, t_1 \in T$ be two points such that, for $i = 0, 1$,
--
--   1. the fibre $p^{-1}(t_i)$ is a finite set, and
--   2. $p$ is flat at every point of that fibre: for every $z \in Z$ with $p(z) = t_i$ the local homomorphism $\mathcal{O}_{T, t_i} \to \mathcal{O}_{Z, z}$ is flat.
--
--   For $i = 0, 1$ let $c_i : S_i \to T$ be any morphism of schemes that maps every point of $S_i$ to $t_i$ (for example $\operatorname{Spec} \kappa(t_i) \to T$, or $\operatorname{Spec} \Omega \to T$ for a field $\Omega \supseteq \kappa(t_i)$), and let
--
--   $$P_i = Z \times_T S_i \xrightarrow{\ q_i\ } S_i$$
--
--   be the base change of $p$ along $c_i$. Then for all $s_0 \in S_0$ and $s_1 \in S_1$ the degrees of $q_0$ and $q_1$ agree (both are finite flat, as base changes of $p$ over a neighbourhood of $t_i$ on which $p$ is finite flat):
--
--   $$\deg_{s_0}(q_0) = \deg_{s_1}(q_1).$$
--
--   In particular, with $S_i = \operatorname{Spec} \kappa(t_i)$, the fibres have the same degree: $\dim_{\kappa(t_0)} \Gamma(p^{-1}(t_0), \mathcal{O}) = \dim_{\kappa(t_1)} \Gamma(p^{-1}(t_1), \mathcal{O})$, and over an algebraically closed $\Omega$ this is the number of points of the geometric fibre counted with multiplicity. This is the principle of conservation of number. The proof: a proper morphism with finite fibre over $t_i$ is finite over a neighbourhood of $t_i$; the flat locus of a finite morphism over a locally noetherian base is open, so $p$ is finite flat over an open $V_i \ni t_i$; since $T$ is irreducible, $V_0 \cap V_1$ is nonempty; and the degree of a finite flat morphism is locally constant, hence constant on the irreducible (so connected) opens $V_0$ and $V_1$, and both equal its value at a point of $V_0 \cap V_1$.
--
--   **Formalization Note**: the degree is Mathlib's `AlgebraicGeometry.Scheme.Hom.finrank` (the rank of $q_{i*}\mathcal{O}_{P_i}$ at a point, defined through an affine chart); the conclusion is `snd₀.finrank s₀ = snd₁.finrank s₁`. The base change is given by any pullback square `CategoryTheory.IsPullback fst₀ snd₀ p c₀` with `∀ s, c₀ s = t₀` (and likewise for $t_1$), so no particular choice of fibre scheme is imposed. Flatness at the fibre points is `(p.stalkMap z).hom.Flat` for every `z` with `p z = t₀`; finiteness of the fibre is `(p ⁻¹' {t₀}).Finite`. All schemes live in one universe `u`. The statement is not vacuous: for example $Z = T = \operatorname{Spec} k$, $p = \mathrm{id}$, $S_i = T$, where both degrees are $1$; more interestingly any finite flat surjection of irreducible noetherian schemes, such as $\operatorname{Spec} \mathbb{Z}[i] \to \operatorname{Spec} \mathbb{Z}$, where the degree is $2$ at every fibre (split, inert or ramified).
-- source:
--   W. Fulton, Intersection Theory, Springer (1984), Chapter 10 (families of algebraic cycles, conservation of number); R. Hartshorne, Algebraic Geometry, Springer GTM 52 (1977), Chapter III, Section 9 (flat morphisms); The Stacks Project, chapter Morphisms of Schemes, section on finite locally free morphisms (locally constant degree)

import Mathlib

set_option autoImplicit false

universe u

theorem AlgebraicGeometry.Scheme.Hom.finrank_fibre_eq_of_isProper_of_flat
    {Z T P₀ S₀ P₁ S₁ : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ T) [AlgebraicGeometry.IsProper p]
    [AlgebraicGeometry.IsLocallyNoetherian T] [IrreducibleSpace T] (t₀ t₁ : T)
    (hfin₀ : (p ⁻¹' {t₀}).Finite) (hfin₁ : (p ⁻¹' {t₁}).Finite)
    (hflat₀ : ∀ z, p z = t₀ → (p.stalkMap z).hom.Flat)
    (hflat₁ : ∀ z, p z = t₁ → (p.stalkMap z).hom.Flat)
    (fst₀ : P₀ ⟶ Z) (snd₀ : P₀ ⟶ S₀) (c₀ : S₀ ⟶ T) (h₀ : CategoryTheory.IsPullback fst₀ snd₀ p c₀)
    (hc₀ : ∀ s, c₀ s = t₀)
    (fst₁ : P₁ ⟶ Z) (snd₁ : P₁ ⟶ S₁) (c₁ : S₁ ⟶ T) (h₁ : CategoryTheory.IsPullback fst₁ snd₁ p c₁)
    (hc₁ : ∀ s, c₁ s = t₁) (s₀ : S₀) (s₁ : S₁) :
    snd₀.finrank s₀ = snd₁.finrank s₁ := by
  sorry
