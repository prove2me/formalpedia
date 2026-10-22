-- Prove2me | Theorems.Thm_FibAnyon_Approx_lemma_5
-- name    : FibAnyon.Approx.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:19.27433+00:00
-- url     : https://prove2.me/theorems/6745fb44-adc5-43a7-a5ad-795f421aafba
-- title:
--   Lemma 5, p. 4 — a decreasing exact-synthesis step, the asymptotic ratio bound (b), and the uniform ratio bound
-- statement:
--   Let $G(x)=|x|^2+|x^\bullet|^2$ be the Gauss complexity of $x\in\mathbb Z[\omega]$, $\tau=(\sqrt5-1)/2$ and $\varphi=\tau^{-1}$. There is a function $r$ with $r(n)=O(1/n)$ as $n\to\infty$ such that for all $u,v\in\mathbb Z[\omega]$ with $|u|\ne0$, $|u|\ne1$ and $|u|^2+\tau|v|^2=1$ there is an integer $k_0$ with
--
--   $$\text{(a)}\ \frac{G((u+\omega^{k_0}v)\tau)}{G(u)}<1,\qquad \text{(b)}\ \frac{G((u+\omega^{k_0}v)\tau)}{G(u)}<\frac{\varphi^2}{2}\bigl(\sqrt[4]{5}-1\bigr)^2+r(G(u)).$$
--
--   In addition, for every integer $k$ the ratio $G((u+\omega^kv)\tau)/G(u)$ is at most $\frac{3\varphi^2}{2}(1+\sqrt\tau)^2$. Clause (a) makes each step of exact synthesis decrease the integer $G$; clause (b) gives the geometric decrease behind the $O(\log G)$ length bound, and the uniform bound gives the matching lower bound.
--
--   **Formalization Note** The function $r$ is chosen once, before $u$ and $v$, and the same $k_0$ satisfies (a) and (b), as in the lemma. $O(1/n)$ is `Asymptotics.IsBigO` at `Filter.atTop` on $\mathbb R$; $\sqrt[4]5$ is written $\sqrt{\sqrt5}$.
-- source:
--   Kliuchnikov, Bocharov, Svore, Asymptotically optimal topological quantum compiling, arXiv:1310.4150v1, p. 4, Lemma 5

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

namespace FibAnyon.Approx

/-- Lemma 5, p. 4: one k₀ giving (a) and (b), with r = O(1/n) fixed before u, v; and the
uniform bound for every k. -/
theorem lemma_5 :
    ∃ r : ℝ → ℝ, r =O[Filter.atTop] (fun n : ℝ => 1 / n) ∧
      ∀ (u v : ZOmega), ‖u.toC‖ ≠ 0 → ‖u.toC‖ ≠ 1 → IsExact u v →
        (∃ k₀ : ℤ,
          gaussG ((u + ZOmega.wpow k₀ * v) * ZOmega.tauZ) / gaussG u < 1 ∧
          gaussG ((u + ZOmega.wpow k₀ * v) * ZOmega.tauZ) / gaussG u <
            gold^2 / 2 * (Real.sqrt (Real.sqrt 5) - 1)^2 + r (gaussG u)) ∧
        (∀ k : ℤ,
          gaussG ((u + ZOmega.wpow k * v) * ZOmega.tauZ) / gaussG u ≤
            3 * gold^2 / 2 * (1 + Real.sqrt tau)^2) := by sorry

end FibAnyon.Approx
