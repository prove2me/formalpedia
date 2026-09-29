-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete
-- name    : AlgebraicGeometry.exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/79aedfe0-fb64-597a-ba56-8c573bff40a7
-- title:
--   Finiteness and algebraisation of compatible systems of Xₙ-schemes
-- statement:
--   Let $R$ be a Noetherian commutative ring, $\varpi \in R$, and assume $R$ is complete and separated for the adic topology of the ideal $(\varpi)$; let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a proper morphism. Assume given, for each $n \in \mathbb{N}$, a morphism $sR_n : \operatorname{Spec}(R/(\varpi^{n+1})) \to \operatorname{Spec} R$ which is $\operatorname{Spec}$ of the quotient map $R \to R/(\varpi^{n+1})$, and transition morphisms $tR_n : \operatorname{Spec}(R/(\varpi^{n+1})) \to \operatorname{Spec}(R/(\varpi^{n+2}))$ with $tR_n$ followed by $sR_{n+1}$ equal to $sR_n$; further, morphisms $x_n$ from the fibre product $X_n := X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/(\varpi^{n+1}))$ to $X_{n+1}$ compatible with the first projections to $X$ and, on second projections, with $tR_n$. Assume given schemes $Y_n$, morphisms $g_n : Y_n \to X_n$ such that each composite of $g_n$ with the second projection $X_n \to \operatorname{Spec}(R/(\varpi^{n+1}))$ is proper, morphisms $y_n : Y_n \to Y_{n+1}$ such that the square with edges $y_n$, $g_n$, $g_{n+1}$, $x_n$ is cartesian, and the hypothesis that each $g_n$ is injective on $K$-points for every algebraically closed field $K$ (two morphisms $\operatorname{Spec} K \to Y_n$ agreeing after $g_n$ coincide). The conclusion is that every $g_n$ is a finite morphism, and that there exist a scheme $Y$, a finite morphism $G : Y \to X$ and morphisms $\varphi_n : Y_n \to Y$ such that each square with edges $\varphi_n$, $g_n$, $G$ and the first projection $X_n \to X$ is cartesian, and $y_n$ followed by $\varphi_{n+1}$ equals $\varphi_n$.
--
--   This combines Zariski's main theorem in Grothendieck's form (a proper, universally injective, hence locally quasi-finite, morphism is finite) with Grothendieck's existence theorem for coherent sheaves over a complete Noetherian base, in the shape needed to algebraise a compatible system of finite covers of the $\varpi$-adic truncations $X_n$ of a proper $R$-scheme $X$ into a single finite cover of $X$. It is used in the analysis of the Čerednik–Drinfeld uniformisation, where the existence of charts and the description of adic points of a quotient are deduced from such a system.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ϖ : R) [IsAdicComplete (Ideal.span {ϖ}) R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n))
    [∀ n : ℕ, IsProper (g n ≫ Limits.pullback.snd f (sR n))]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n))
    (hinj : ∀ (n : ℕ) (K : Type u) [Field K] [IsAlgClosed K] (y y' : Spec (CommRingCat.of K) ⟶ Y n),
      y ≫ g n = y' ≫ g n → y = y') :

    (∀ n : ℕ, IsFinite (g n)) ∧

    ∃ (Yf : Scheme.{u}) (G : Yf ⟶ X) (_ : IsFinite G) (φ : ∀ n : ℕ, Y n ⟶ Yf),
      (∀ n : ℕ, IsPullback (φ n) (g n) G (Limits.pullback.fst f (sR n))) ∧
      (∀ n : ℕ, yn n ≫ φ (n + 1) = φ n) := by sorry
