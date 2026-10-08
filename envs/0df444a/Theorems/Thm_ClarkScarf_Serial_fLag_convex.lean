-- Prove2me | Theorems.Thm_ClarkScarf_Serial_fLag_convex
-- name    : ClarkScarf.Serial.fLag_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:28:05.367094+00:00
-- url     : https://prove2.me/theorems/d7580f8c-acdd-4f8a-b3e5-5a748bfac424
-- title:
--   §2, p. 478, item 3 — the functions fₙ of (7) are convex
-- statement:
--   Let $f_n$ be the functions of (7) for installation 1 of the two-installation model: $f_n\equiv0$ for $n\le2$ and, for $n\ge3$,
--   $$f_n(u)=\inf_{y\ge u}\Big\{c_1(y-u)+\alpha^2\int_0^\infty\!\!\int_0^\infty L(y-t_1-t_2)\varphi(t_1)\varphi(t_2)\,dt_2\,dt_1+\alpha\int_0^\infty f_{n-1}(y-t)\varphi(t)\,dt\Big\},$$
--   with linear shipping cost $c_1\ge0$ (no setup cost). Then for every $n$, $f_n$ is a convex function on $\mathbb R$.
--
--   Convexity of $f_n$ is what makes the optimal shipment policy of installation 1 a single critical number $\bar x_n$, and it is used to show that a constrained installation 1 should ship as much as it can.
--
--   **Formalization Note** Only the convexity clause of item 3 is formalized; the paper's additional claim $f_n'(u)=-c$ for $u\le\bar x_n$ (cited from its Reference 2) is not part of this item. In (7) the shipping cost $c_1$ plays the role of the setup-free purchase cost of item 3.
-- source:
--   Clark and Scarf, Optimal Policies for a Multi-Echelon Inventory Problem, Management Sci. 6(4), 1960, p. 478, §2 item 3 (convexity of f_n), applied to eq. (7) p. 480

import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- §2, p. 478, item 3 (convexity clause), for the functions `f_n` of (7): every `f_n` is convex. -/
theorem fLag_convex (M : Model) (n : ℕ) : ConvexOn ℝ univ (M.fLag n) := by sorry

end ClarkScarf.Serial
