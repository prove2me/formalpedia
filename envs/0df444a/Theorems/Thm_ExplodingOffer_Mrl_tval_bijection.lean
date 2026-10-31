-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_tval_bijection
-- name    : ExplodingOffer.Mrl.tval_bijection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:34.855774+00:00
-- url     : https://prove2.me/theorems/676c3843-7dfa-4a0b-9672-361594f72787
-- title:
--   Proof of Lemma 8, p. 33 — ℒ > 0 below b, and 𝒯 is a strictly increasing bijection [0, b) → [0, ∞)
-- statement:
--   Let $X$ be a nonnegative continuous random variable with support $[a, b]$ ($0 \le a \le b$, $b \ne 0$, $b \le +\infty$) and finite mean, let $\mathcal L(v) = \mathbb E[(X - v)^+]$ and $\mathcal T(V) = \int_0^V dv/\mathcal L(v)$. Then:
--
--   1. $\mathcal L(v) > 0$ for every $0 \le v < b$;
--   2. $\mathcal T$ is strictly increasing on $[0, b)$;
--   3. for every $y \ge 0$, $\mathcal T^{-1}(y)$ lies in $[0, b)$ and $\mathcal T(\mathcal T^{-1}(y)) = y$;
--   4. $\mathcal T^{-1}(\mathcal T(V)) = V$ for every $V \in [0, b)$.
--
--   In short, $\mathcal T$ maps $[0,b)$ bijectively onto $[0,\infty)$:
--   $$\mathcal T : [0, b) \xrightarrow{\ \sim\ } [0, \infty).$$
--
--   This is what makes the operator $\mathcal T^{-1}$ in the closed-form value-to-go (2) well defined, and it gives $v(t_D) < b$ in Lemma 1.
--
--   **Formalization Note** $\mathcal T^{-1}(y)$ is defined as the supremum of $\{V \in [0,b) : \mathcal T(V) \le y\}$; this theorem shows that it is the inverse of $\mathcal T$. Surjectivity onto $[0,\infty)$ is the paper's divergence $\int^b dv/\mathcal L(v) = +\infty$.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), p. 33, proof of Lemma 8

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem tval_bijection {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) :
    (∀ v : ℝ, 0 ≤ v → (v : EReal) < b → 0 < Lfun μ v) ∧
    StrictMonoOn (Tval μ) {V : ℝ | 0 ≤ V ∧ (V : EReal) < b} ∧
    (∀ y : ℝ, 0 ≤ y →
      0 ≤ Tinv μ b y ∧ (Tinv μ b y : EReal) < b ∧ Tval μ (Tinv μ b y) = y) ∧
    (∀ V : ℝ, 0 ≤ V → (V : EReal) < b → Tinv μ b (Tval μ V) = V) := by sorry

end ExplodingOffer.Mrl
