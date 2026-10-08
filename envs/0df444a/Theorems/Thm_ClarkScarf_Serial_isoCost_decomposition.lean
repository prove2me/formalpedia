-- Prove2me | Theorems.Thm_ClarkScarf_Serial_isoCost_decomposition
-- name    : ClarkScarf.Serial.isoCost_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:29:03.075888+00:00
-- url     : https://prove2.me/theorems/2b7191be-a192-4ae3-b263-70ae471e09e0
-- title:
--   Eqs. (6)–(7), p. 480 — Ĉₙ(x₁, w₁) = L(x₁) + α∫L(x₁+w₁−t)φ(t)dt + fₙ(x₁+w₁) for n ≥ 2
-- statement:
--   In the two-installation model, let $\hat C_n(x_1,w_1)$ be the optimal $n$-period cost of installation 1 operated in isolation, eq. (15): $x_1$ is the stock on hand, $w_1$ the stock arriving next period, shipments cost $c_1$ per unit and arrive after two periods. Let $f_n$ be the functions of (7), with $f_n\equiv0$ for $n\le2$. Then for every $n\ge2$ and all real $x_1,w_1$,
--   $$\hat C_n(x_1,w_1)=L(x_1)+\alpha\int_0^\infty L(x_1+w_1-t)\varphi(t)\,dt+f_n(x_1+w_1).$$
--
--   The first two terms are the costs of the current and the next period, which no shipment requested now can change; $f_n$ collects everything a shipment can influence, and depends on the state only through the inventory position $x_1+w_1$.
--
--   **Formalization Note** The paper states the case $n=2$ (where $f_2\equiv 0$) separately and (6) for $n>2$; with $f_2\equiv0$ the two are one statement.
-- source:
--   Clark and Scarf, Optimal Policies for a Multi-Echelon Inventory Problem, Management Sci. 6(4), 1960, p. 480, eqs. (6)-(7) and the preceding sentence on C₂

import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Eqs. (6)–(7), p. 480: for `n ≥ 2` periods remaining the isolated installation-1 cost splits
as `Ĉ_n(x₁, w₁) = L(x₁) + α ∫₀^∞ L(x₁ + w₁ - t) φ(t) dt + f_n(x₁ + w₁)`. -/
theorem isoCost_decomposition (M : Model) (n : ℕ) (hn : 2 ≤ n) (x₁ w₁ : ℝ) :
    M.isoCost n x₁ w₁ =
      M.L x₁ + M.α * (∫ t in Ioi (0 : ℝ), M.L (x₁ + w₁ - t) * M.φ t) + M.fLag n (x₁ + w₁) := by sorry

end ClarkScarf.Serial
