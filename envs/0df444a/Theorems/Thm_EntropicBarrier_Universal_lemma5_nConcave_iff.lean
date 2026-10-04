-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_lemma5_nConcave_iff
-- name    : EntropicBarrier.Universal.lemma5_nConcave_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:03:31.959976+00:00
-- url     : https://prove2.me/theorems/4c441f4f-a97d-4c12-9a09-1e220ecf2548
-- title:
--   Lemma 5 — $\varphi$ is $n$-concave on $(a,b)$ $\iff$ $\zeta''\le-\frac1n(\zeta')^2$ for $\zeta=\log\varphi$
-- statement:
--   Let $a,b\in\mathbb R$, $n>0$, and let $\varphi\in C^2((a,b))$ be positive on $(a,b)$, with $\zeta(x)=\log\varphi(x)$. Then
--   $$\varphi\text{ is }n\text{-concave in }(a,b)\iff\zeta''\le-\frac1n(\zeta')^2\text{ in }(a,b).$$
--
--   This turns the $n$-concavity of the section marginal into the differential inequality used in the proof of Lemma 3.
--
--   **Formalization Note** Positivity of $\varphi$ on $(a,b)$ is implicit on the page ($\zeta=\log\varphi$). The lemma is stated for every real $n>0$; the paper uses it with $n$ the dimension. Derivatives are Mathlib's `deriv`, taken of $\zeta=\log\circ\varphi$; at points of the open interval they are the true first and second derivatives.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 9, Lemma 5 (restated and proved p. 13)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_Marginal

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem lemma5_nConcave_iff (n a b : ℝ) (hn : 0 < n) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioo a b)) (hpos : ∀ x ∈ Set.Ioo a b, 0 < φ x) :
    IsNConcaveOn n (Set.Ioo a b) φ ↔
      ∀ x ∈ Set.Ioo a b,
        deriv (deriv (fun t => Real.log (φ t))) x ≤
          -(1 / n) * (deriv (fun t => Real.log (φ t)) x) ^ 2 := by sorry

end EntropicBarrier.Universal
