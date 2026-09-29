-- Prove2me | Theorems.Thm_Erdos30_erdos_30
-- name    : Erdos30.erdos_30
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:41:19.645871+00:00
-- url     : https://prove2.me/theorems/cee1e460-f138-4910-ac15-f5a8fa83964a
-- title:
--   Erdős Problem 30: $h(N)=\sqrt N+O_\varepsilon(N^\varepsilon)$
-- statement:
--   Let $h(N)$ be the maximum size of a Sidon set contained in $\{1,\dots,N\}$. Then for every real $\varepsilon>0$,
--
--   $$h(N)=\sqrt N+O_{\varepsilon}\!\left(N^{\varepsilon}\right)\qquad(N\to\infty),$$
--
--   that is, there are constants $C_\varepsilon$ and $N_\varepsilon$ with $|h(N)-\sqrt N|\le C_\varepsilon N^{\varepsilon}$ for all $N\ge N_\varepsilon$.
--
--   This is the question of Erdős and Turán (Erdős Problem #30, \$1000), still open. The formal-conjectures entry states it as `answer(sorry) ↔ …`; here the answer is fixed to the conjectured **yes**, so a proof settles it affirmatively and a disproof (a proof of the negation) settles it negatively. The best known upper bound is $\sqrt N+0.98183N^{1/4}+O(1)$; from below, $h(N)\ge(1-o(1))\sqrt N$ (Singer).
--
--   **Formalization Note** The $O(\cdot)$ is Mathlib's `IsBigO` along `atTop` for functions $\mathbb N\to\mathbb R$; $h(N)$ is cast to $\mathbb R$ and $N^{\varepsilon}$ is the real power.
-- source:
--   Erdős Problem #30, https://www.erdosproblems.com/30 (cited there as [Er61], [Er69], … , [Va99, 1.18]); formal-conjectures FormalConjectures/ErdosProblems/30.lean (theorem erdos_30); the `answer(sorry)` placeholder is instantiated to `True` (the conjectured answer).

import Mathlib
import Definitions.Def_Erdos30Basic

open Filter Asymptotics

namespace Erdos30

theorem erdos_30 :
    ∀ᵉ (ε > (0 : ℝ)),
      (fun N : ℕ => (h N : ℝ) - Real.sqrt N) =O[atTop] fun N : ℕ => (N : ℝ) ^ (ε : ℝ) := by
  sorry

end Erdos30
