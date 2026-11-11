-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_G_1
-- name    : DiffusionErrorAcc.Stability.lemma_G_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:58:19.994131+00:00
-- url     : https://prove2.me/theorems/773822b5-ef40-43d5-ac71-ef9461781078
-- title:
--   Lemma G.1 — divergence theorem on ℝ^d: ∫ ∇·F = 0 for C¹ F with F, ∇·F integrable
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R^d$ be a continuously differentiable vector field. If $F$ and its divergence $\nabla\cdot F=\sum_i\partial_iF_i$ are absolutely integrable over $\mathbb R^d$, then
--   $$\int_{\mathbb R^d}\nabla\cdot F(x)\,dx=0 .$$
--   This whole-space divergence theorem is the integration-by-parts step of Lemma F.1.
--
--   **Formalization Note.** The integral is the Lebesgue integral on `EuclideanSpace ℝ (Fin d)`; $d\ge1$ is the paper's standing assumption.
--
--   Differences from the source: none.
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 37, Lemma G.1

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_Densities

open MeasureTheory

namespace DiffusionErrorAcc.Stability

/-- Lemma G.1 (divergence theorem, p. 37). Let `F : ℝ^d → ℝ^d` be a continuously differentiable
vector field. If `F` and `∇ · F` are absolutely integrable, then `∫_{ℝ^d} ∇ · F(x) dx = 0`. -/
theorem lemma_G_1 {d : ℕ} (hd : 1 ≤ d) (F : Rd d → Rd d) (hF : ContDiff ℝ 1 F)
    (hFi : Integrable F) (hdivi : Integrable (divergence F)) :
    ∫ x, divergence F x = 0 := by sorry

end DiffusionErrorAcc.Stability
