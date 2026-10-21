-- Prove2me | Theorems.Thm_EarlyInspect_Align_lemma_1
-- name    : EarlyInspect.Align.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:22.672983+00:00
-- url     : https://prove2.me/theorems/a60d7741-d5d8-4bd0-b90a-67a3dd3f9ca7
-- title:
--   Lemma 1, p. 63 — above e^{−½k²(1−t)}√tσ/k, ω has exactly one local minimum; otherwise ω(−k) ≤ ω(z) for all z ≥ −k
-- statement:
--   Let $\mu>0$, $\sigma>0$, $t\in(0,1)$ and a penalty $M\ge0$, write $k=\mu/\sigma$, $a=k(1-t)$, and let
--   $$\omega(z)=\Phi(z)-\frac{M}{\sqrt t\,\sigma}\,\varphi\!\left(\frac{a+z}{\sqrt t}\right),\qquad z\in\mathbb R,$$
--   be the derivative of the agent's score in eq. (9). Then:
--
--   1. if $M>\dfrac{e^{-\frac12 k^2(1-t)}\sqrt t\,\sigma}{k}$, then $\omega$ has exactly one local minimum on $\mathbb R$;
--   2. otherwise, that is if $M\le\dfrac{e^{-\frac12 k^2(1-t)}\sqrt t\,\sigma}{k}$, then $\omega(-k)\le\omega(z)$ for every $z\ge-k$.
--
--   The point $z=-k$ corresponds to the order-up-to level $S=0$, so the second clause says that on the feasible stock levels $\omega$ is smallest at an empty shelf. The lemma is the shape information behind Theorem 3.
--
--   **Formalization Note** Two hypotheses are added to the page. $\mu>0$ (so $k>0$): the threshold divides by $k$, and the paper's demand has positive mean (p. 58). $M\ge0$: $M$ is a stock-out penalty, and the principal's problem $PP^{Mt}$ optimizes over $M\ge0$ (p. 63); for $M<0$ the second clause fails (e.g. $\mu=\sigma=1$, $t=1/2$, $M=-5$ gives $\omega(-k)\approx2.36$ while $\omega(z)\to1$ as $z\to\infty$). "Has only one local finite minimum" is read on all of $\mathbb R$ as the existence and uniqueness of a point where $\omega$ has a local minimum.
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), p. 63 (PDF 10), Lemma 1

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

namespace EarlyInspect.Align

theorem lemma_1 (μ σ M t : ℝ) (hμ : 0 < μ) (hσ : 0 < σ) (ht : 0 < t) (ht1 : t < 1)
    (hM : 0 ≤ M) :
    (Real.exp (-(1 / 2) * ((μ / σ) ^ 2 * (1 - t))) * Real.sqrt t * σ / (μ / σ) < M →
        ∃! z₀ : ℝ, IsLocalMin (omega μ σ M t) z₀) ∧
      (M ≤ Real.exp (-(1 / 2) * ((μ / σ) ^ 2 * (1 - t))) * Real.sqrt t * σ / (μ / σ) →
        ∀ z : ℝ, -(μ / σ) ≤ z → omega μ σ M t (-(μ / σ)) ≤ omega μ σ M t z) := by sorry

end EarlyInspect.Align
