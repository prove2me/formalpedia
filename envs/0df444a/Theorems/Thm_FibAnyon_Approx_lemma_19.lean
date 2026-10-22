-- Prove2me | Theorems.Thm_FibAnyon_Approx_lemma_19
-- name    : FibAnyon.Approx.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:30.250042+00:00
-- url     : https://prove2.me/theorems/ddd9b1f1-d78c-4911-b81d-318383847c3f
-- title:
--   Lemma 19, p. 13 (corrected: G(u₀)=O(1/ε²)) — RANDOM-SAMPLE: O(1/ε) equiprobable outputs, all in the parallelogram P
-- statement:
--   Let RANDOM-SAMPLE$(\theta,\varepsilon,r)$ be the procedure of Figure 13, with $m=\lceil\log_\tau(C\varepsilon r)\rceil+1$, $C=\sqrt{\varphi/(4r)}$, $N=\lceil\varphi^m\rceil$, and its random integer $j$ drawn uniformly from $[1,N-1]$. Let $P$ be the dark gray parallelogram of Figure 14: the points $z$ with $y_{\min}\le\operatorname{Im}z\le y_{\max}$ and
--
--   $$r\varphi^m(1-\varepsilon^2)\le\operatorname{Re}(z e^{-i\theta})\le r\varphi^m(1-\varepsilon^2/2).$$
--
--   For every $r\ge1$ there is a constant $K_0>0$ such that for all $\theta\in[0,\pi/5]$ and $\varepsilon\in(0,1/2]$: the procedure has at most $K_0/\varepsilon$ different outputs, each produced by the same number of indices $j$ (so each occurs with the same probability); every output $u_0\in\mathbb Z[\omega]$ lies in $P$; and $G(u_0)\le K_0/\varepsilon^2$. Membership in $P$ is what gives the approximation precision in Theorem 21, and the complexity bound gives the circuit length.
--
--   **Formalization Note** The random index is an explicit argument $j\in[1,N-1]$; "each output occurs with the same probability" is stated as equal fibre sizes of $j\mapsto u_0$ over that range. The range $0<\varepsilon\le1/2$ is added (the paper's $\varepsilon$ is a small precision; at $r=5$, $\varepsilon=0.9$ the region claim fails). The printed third bullet says $G(u_0)=O(1/\varepsilon)$; this is corrected to $O(1/\varepsilon^2)$, which is what the paper's own proof gives ($u_0$'s coefficients are $O(\varphi^m)=O(1/\varepsilon)$ and $G\le\frac52\sum\alpha_k^2$), and the printed bound is false since $G(u_0)\ge|u_0|^2=\Theta(1/\varepsilon^2)$. Figure 13 is used with the corrected sign of the second term of $x_{\max}$. $K_0$ may depend on $r$.
-- source:
--   Kliuchnikov, Bocharov, Svore, Asymptotically optimal topological quantum compiling, arXiv:1310.4150v1, p. 13, Lemma 19; Figures 13–14, p. 12 (G bound corrected)

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

namespace FibAnyon.Approx

/-- Lemma 19, p. 13, for every r ≥ 1 and 0 < ε ≤ 1/2: over the admissible indices
j ∈ [1, N − 1] there are O(1/ε) distinct outputs, each produced by equally many indices
(equal probability for uniform j); every output lies in the parallelogram P of Figure 14;
and G(u₀) = O(1/ε²) (corrected from the printed O(1/ε)). -/
theorem lemma_19 :
    ∀ r : ℝ, 1 ≤ r → ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ (θ ε : ℝ), 0 ≤ θ → θ ≤ Real.pi / 5 → 0 < ε → ε ≤ 1/2 →
        let J := Finset.Icc 1 (sampleN ε r - 1)
        (((J.image (randomSample θ ε r)).card : ℝ) ≤ K₀ / ε ∧
          ∀ j₁ ∈ J, ∀ j₂ ∈ J,
            (J.filter (fun j => randomSample θ ε r j = randomSample θ ε r j₁)).card =
              (J.filter (fun j => randomSample θ ε r j = randomSample θ ε r j₂)).card) ∧
        ∀ j ∈ J,
          (randomSample θ ε r j).toC ∈ parallelogramP θ ε r ∧
          gaussG (randomSample θ ε r j) ≤ K₀ / ε^2 := by sorry

end FibAnyon.Approx
