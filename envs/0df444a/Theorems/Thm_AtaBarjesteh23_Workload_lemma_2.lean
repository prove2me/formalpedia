-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_lemma_2
-- name    : AtaBarjesteh23.Workload.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:39.613856+00:00
-- url     : https://prove2.me/theorems/e0075050-f87c-4e44-9dab-0e5f0d9822a2
-- title:
--   Lemma 2, p. 18 — the conjugate of c is φ(y) = (m′H⁻¹m/4)y², maximized uniquely at ψ(y) = (m′H⁻¹m/2)y
-- statement:
--   Let $\varphi(y)=\sup_{x\in\mathbb R}\{yx-c(x)\}$ be the convex conjugate of the drift cost $c$ and $\psi(y)$ the maximizer (40). Under the standing assumptions, for every $y\in\mathbb R$,
--   $$\varphi(y)=\frac{m'H^{-1}m}{4}\,y^2\qquad\text{and}\qquad \psi(y)=\frac{m'H^{-1}m}{2}\,y. \tag{41}$$
--   Precisely: $\frac a4y^2$ is the greatest value of $x\mapsto yx-c(x)$, and $x$ attains it if and only if $x=\frac a2y$.
--
--   Lemma 2 rewrites the Bellman equation (37) as the Riccati equation (43) and identifies the optimal drift rate (56).
--
--   **Formalization Note** The supremum is stated as attained (`IsGreatest`), and $\psi$ as the unique maximizer.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 18, Lemma 2, (40)–(41)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem lemma_2 (M : Model) (hM : M.Standing) (y : ℝ) :
    IsGreatest (range fun x : ℝ => y * x - M.cost x) (M.a / 4 * y ^ 2) ∧
    ∀ x : ℝ, y * x - M.cost x = M.a / 4 * y ^ 2 ↔ x = M.a / 2 * y := by sorry

end AtaBarjesteh23.Workload
