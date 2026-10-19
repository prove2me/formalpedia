-- Prove2me | Theorems.Thm_FlatlyFoliated_theorem2_equivalence
-- name    : FlatlyFoliated.theorem2_equivalence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T20:39:53.480348+00:00
-- url     : https://prove2.me/theorems/30907190-4d1d-4f16-8649-df58ca44cb71
-- title:
--   Theorem 2 — FFR equations ⟺ elliptic form
-- statement:
--   Fix $\Lambda\in\mathbb R$ and smooth $\mu:\mathbb R^3\to\mathbb R$, $J:\mathbb R^3\to\mathbb R^3$, $\eta:\mathbb R^3\to\mathbb R$ with $\eta>0$.
--
--   1. If smooth $(\omega,\eta)$ solve the FFR equations (34)–(35) and a smooth $f$ solves $\Delta f=\nabla\cdot\omega$, then with $\zeta=\omega-df$ the triple $(f,\zeta,\eta)$ solves the elliptic form (39)–(41), including $\lim_{x\to\infty}\nabla\cdot\zeta=0$.
--   2. Conversely, if smooth $(f,\zeta,\eta)$ solve (39)–(41) together with $\lim_{x\to\infty}\nabla\cdot\zeta=0$, then $\omega=df+\zeta$ solves (34)–(35) and $\Delta f=\nabla\cdot\omega$.
--
--   This is what allows the elliptic system to replace the original FFR equations.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 10, Theorem 2 (equations (34), (35), (37)–(41))

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Theorem 2: equivalence of (34)–(35) (+ a solution of `Δf = ∇·ω`) with the elliptic
form (39)–(41) (+ `lim ∇·ζ = 0`), via `w = df + ζ`. -/
theorem theorem2_equivalence (Λ : ℝ) (μ : R3 → ℝ) (J : R3 → R3) (η : R3 → ℝ)
    (hμ : ContDiff ℝ ∞ μ) (hJ : ContDiff ℝ ∞ J) (hη : ContDiff ℝ ∞ η)
    (hηpos : ∀ x, 0 < η x) :
    (∀ (w : R3 → R3) (f : R3 → ℝ), ContDiff ℝ ∞ w → ContDiff ℝ ∞ f →
        FFREquations Λ μ J w η → (∀ x, lap f x = divg w x) →
        EllipticSystem Λ μ J f (fun x => w x - grad f x) η) ∧
    (∀ (f : R3 → ℝ) (ζ : R3 → R3), ContDiff ℝ ∞ f → ContDiff ℝ ∞ ζ →
        EllipticSystem Λ μ J f ζ η →
        FFREquations Λ μ J (fun x => grad f x + ζ x) η ∧
          ∀ x, lap f x = divg (fun y => grad f y + ζ y) x) := by sorry

end FlatlyFoliated
