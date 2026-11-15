-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_recursion_prefix
-- name    : AppliedSDE.SarkkaSolin.ar1_kalman_recursion_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:03:02.615028+00:00
-- url     : https://prove2.me/theorems/081a628d-c3b5-4d05-a177-8deaf4fa4cea
-- title:
--   Prefix restriction preserves each indexed scalar AR1 Kalman mean and variance recursion
-- statement:
--   A scalar Kalman mean/variance recursion on n+2 observations restricts to the identical recursion on the first n+1 observations. This is the exact Fin.castSucc index transport required for induction proving GP batch and sequential Kalman equality.
-- source:
--   Sarkka and Solin (2019), discrete-time AR1 Kalman recursion; Lean Fin prefix restriction.

import Mathlib

theorem AppliedSDE.SarkkaSolin.ar1_kalman_recursion_prefix
    (n : ℕ) (a V r : ℝ)
    (y m P : Fin (n + 2) -> ℝ)
    (hstep : ∀ j : Fin (n + 1),
      let pred : ℝ := a ^ 2 * P j.castSucc + V * (1 - a ^ 2)
      P j.succ = pred * r / (pred + r) ∧
      m j.succ = a * m j.castSucc +
        pred / (pred + r) * (y j.succ - a * m j.castSucc)) :
    let yold : Fin (n + 1) -> ℝ := fun j => y j.castSucc
    let mold : Fin (n + 1) -> ℝ := fun j => m j.castSucc
    let Pold : Fin (n + 1) -> ℝ := fun j => P j.castSucc
    ∀ j : Fin n,
      let pred : ℝ := a ^ 2 * Pold j.castSucc + V * (1 - a ^ 2)
      Pold j.succ = pred * r / (pred + r) ∧
      mold j.succ = a * mold j.castSucc +
        pred / (pred + r) *
          (yold j.succ - a * mold j.castSucc) := by
  sorry
