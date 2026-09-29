-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
-- name    : AlgebraicGeometry.exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/6185fbb2-4e7c-57fe-8378-f1944194c353
-- title:
--   Proper modification making the centre of a valuation one-dimensional
-- statement:
--   Let $k$ be a field, let $P$ be an integral scheme equipped with a morphism $p\colon P \to \operatorname{Spec} k$ that is locally of finite type, and let $O$ be a valuation subring of the function field $k(P)$ (the stalk of $P$ at its generic point) with $O \neq k(P)$. Suppose given a morphism $\ell_0\colon \operatorname{Spec} O \to P$ whose composite with $\operatorname{Spec}$ of the inclusion $O \to k(P)$ is the canonical morphism `P.fromSpecStalk (genericPoint P)`, so that $O$ dominates the local ring of $P$ at the image of the closed point of $O$. Let $d$ be a natural number with $d+1 = \operatorname{topologicalKrullDim} P$ in $\mathbb{N}_\infty$ adjoined a bottom element, and let $f\colon \operatorname{Fin} d \to k(P)$ take values in $O$ and satisfy: for every $Q \in k[X_i : i \in \operatorname{Fin} d]$, if the value under the valuation of $O$ of $Q$ evaluated at $f$, with coefficients pushed along the composite $k \to \Gamma(P,\top) \to k(P)$ of the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism, the global sections of $p$, and the germ map at the generic point, is $< 1$, then $Q = 0$. Then there exist an integral scheme $P'$, a proper morphism $\beta\colon P' \to P$, a non-empty open subscheme $U \subseteq P$, an open immersion $s\colon U \to P'$ with $s$ followed by $\beta$ the inclusion of $U$ and with $\operatorname{range}(s) = \beta^{-1}(U)$ on points, a morphism $\ell\colon \operatorname{Spec} O \to P'$ with $\ell$ followed by $\beta$ equal to $\ell_0$, and a point $y' \in P'$ which is the image of the closed point of $O$ under $\ell$, such that the stalk of $P'$ at $y'$ has Krull dimension $1$.
--
--   This is the valuation-theoretic core of Rosenlicht's lemma preceding his theorem on normal complete models: a valuation of the function field whose residue field contains $d = \dim P - 1$ elements algebraically independent over $k$ becomes, after a proper modification of $P$ that is an isomorphism over a non-empty open set, centred at a point whose local ring is one-dimensional, i.e. at a prime divisor of the new model. It is used in the constructions of proper models with prescribed divisorial behaviour, being cited by [`AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one`](thm.html#AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one) and [`AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper`](thm.html#AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
    (k : Type u) [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsIntegral P] [LocallyOfFiniteType p]
    (O : ValuationSubring P.functionField) (hO : O ≠ ⊤)
    (ℓ₀ : Spec (CommRingCat.of O) ⟶ P)
    (hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
      P.fromSpecStalk (genericPoint P))
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P)
    (f : Fin d → P.functionField) (hf : ∀ i, f i ∈ O)
    (hind : ∀ Q : MvPolynomial (Fin d) k,
      O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) f) < 1 → Q = 0) :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P')
      (ℓ : Spec (CommRingCat.of O) ⟶ P') (y' : P'),
      IsIntegral P' ∧ IsProper β ∧ (U : Set P).Nonempty ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧
      ℓ ≫ β = ℓ₀ ∧ ℓ.base (IsLocalRing.closedPoint O) = y' ∧
      ringKrullDim (P'.presheaf.stalk y') = 1 := by sorry
