-- Prove2me | Theorems.Thm_BranchRepairs_dominated_escape
-- name    : BranchRepairs.dominated_escape
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:28:51.750164+00:00
-- url     : https://prove2.me/theorems/9f0c70f6-89d7-4866-a634-31ac806c4a1c
-- title:
--   dominated escape — BranchRepairs
-- statement:
--   Seja \(f:\mathbb N\times\mathbb N\to\mathbb R\) e seja \(b:\mathbb N\to\mathbb R\) uma sequência somável. Suponha que \(f(m,j)\to0\) para cada \(j\) e que, para todo \(m\) suficientemente grande e todo \(j\), \(|f(m,j)|\le b(j)\). Então
--   $$ \lim_{m\to\infty}\sum_{j=0}^{\infty}f(m,j)=0. $$
--   É uma aplicação da convergência dominada para séries; o majorante somável deve ser estabelecido na aplicação.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. BranchRepairs.dominated_escape; fonte BRANCH_REPAIRS.lean; SHA256 original 044e027c4764608082de3e11b57a2ce18282197670adc8726daa23be725e17f7. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem BranchRepairs.dominated_escape (f : ℕ → ℕ → ℝ) (bound : ℕ → ℝ)
    (hs : Summable bound)
    (hpoint : ∀ j, Tendsto (fun m => f m j) atTop (𝓝 0))
    (hbound : ∀ᶠ m in atTop, ∀ j, ‖f m j‖ ≤ bound j) :
    Tendsto (fun m => ∑' j, f m j) atTop (𝓝 0) := by sorry
