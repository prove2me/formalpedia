-- Prove2me | Theorems.Thm_DictatorsCK_Main_theorem_7_1
-- name    : DictatorsCK.Main.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:43:19.348096+00:00
-- url     : https://prove2.me/theorems/5a3637c3-13dc-4407-8148-17684a90e4e7
-- title:
--   Theorem 7.1 — explicit Talagrand-type bound $\mathrm{Var}(P_Kg)\le\sum_{i\in K}\psi(\|\partial_ig\|_1)$
-- statement:
--   Let $n\ge1$. For every $g:\{-1,1\}^n\to[-1,1]$ and every $K\subseteq[n]$,
--   $$\mathrm{Var}(P_Kg)\le\sum_{i\in K}\psi\big(\|\partial_ig\|_1\big),$$
--   and in particular $\mathrm{Var}(g)\le\sum_i\psi(\|\partial_ig\|_1)$. Here $P_K$ is the coordinate projection (7.1), $\partial_ig$ the half-difference in coordinate $i$, $\|v\|_1=\mathbb E|v|$, and $\psi(a)=\min\{(a+a^2)/2,\ 2a(1-a/4)/\log(4/a)\}$, $\psi(0)=0$ (7.2).
--
--   This is an explicit quantitative form of Talagrand's influence inequality for bounded functions, with the constants needed later.
--
--   Differences from the source:
--   - encoding: real functions on the cube {−1, 1}^n → real functions on Cube n = Fin n → Bool with x_i = 1 ⇔ true; reason: the cube type of the referenced goal; a relabelling of points that changes no instance
--   - encoding: coordinates i ∈ [n] = {1, …, n} → i : Fin n = {0, …, n − 1}; reason: index shift only
--   - encoding: ∂_i h as a function on {−1, 1}^{[n]∖{i}} → halfDiff i h on the full cube, ignoring x_i; reason: the paper itself views ∂_i h this way (p. 9); its norms and expectations are unchanged
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 36 (PDF 37), Theorem 7.1

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Arcsine

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem theorem_7_1 {n : ℕ} (hn : 1 ≤ n) (g : Cube n → ℝ) (hg : ∀ x, -1 ≤ g x ∧ g x ≤ 1)
    (K : Finset (Fin n)) :
    variance (proj K g) ≤ ∑ i ∈ K, talagrandPsi (cubeAverage (fun x => |halfDiff i g x|)) ∧
    variance g ≤ ∑ i, talagrandPsi (cubeAverage (fun x => |halfDiff i g x|)) := by sorry

end DictatorsCK.Main
