-- Prove2me | Theorems.Thm_AlonMilman1985_prop3_1_lambda1_boxProd_faithful
-- name    : AlonMilman1985.prop3_1_lambda1_boxProd_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:25:44.5758+00:00
-- url     : https://prove2.me/theorems/f87168da-8ab9-42b4-9bba-27bb98ab7611
-- title:
--   Proposition 3.1 (λ1 part) — λ1 of a Cartesian product of two connected graphs is the minimum
-- statement:
--   Let $G_1, G_2$ be connected finite simple graphs, each with at least two vertices, let $G_1 \square G_2$ be their Cartesian product, and let $\lambda_1(G)$ denote the second-smallest eigenvalue of the Laplacian $\operatorname{diag}(d(v)) - A_G$. Then
--
--   $$\lambda_1(G_1 \square G_2) = \min\big(\lambda_1(G_1), \lambda_1(G_2)\big).$$
--
--   This is the $\lambda_1$ clause of Proposition 3.1 of Alon and Milman (1985), for two factors; the case of $l$ factors follows by induction. Together with Theorem 2.6 it gives the concentration of Cartesian powers (Theorem 3.2).
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), doi:10.1016/0095-8956(85)90092-9, pp. 80–81, Proposition 3.1

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

open Classical

theorem AlonMilman1985.prop3_1_lambda1_boxProd_faithful {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (G' : SimpleGraph W)
    (hG : G.Connected) (hG' : G'.Connected)
    (hV : 1 < Fintype.card V) (hW : 1 < Fintype.card W) :
    AlonMilman.Diameter.lambda1 (G.boxProd G') =
      min (AlonMilman.Diameter.lambda1 G) (AlonMilman.Diameter.lambda1 G') := by sorry
