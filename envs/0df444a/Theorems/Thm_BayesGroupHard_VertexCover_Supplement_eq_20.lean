-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_Supplement_eq_20
-- name    : BayesGroupHard.VertexCover.Supplement.eq_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T11:43:45.250774+00:00
-- url     : https://prove2.me/theorems/4ba06ade-837a-44a9-8ad5-f75951d143c4
-- title:
--   (20), p. 32 — an element agent reports φ_ε,1 = 3ℓ_1 + 2ℓ_0 iff 2s_κ + Σ_j s_ε(j) = 3
-- statement:
--   Let $\hat{\mathcal G}_n$ be an RXC3 instance and consider the EXACT-COVER reduction network of Appendix B, with subset agents $\tau$ ($\bar p=\tfrac12$, $\underline p=\tfrac13$), element agents $\varepsilon$ observing $\kappa$ and their three subset agents $\varepsilon^{(1)},\varepsilon^{(2)},\varepsilon^{(3)}$, agent $\kappa$ ($\bar p^\star=\tfrac7{12}$, $\underline p^\star=\tfrac7{27}$) and agent $i$. Let $\ell_1=\log\tfrac32$, $\ell_0=\log\tfrac34$. For every signal profile $s$ and every element agent $\varepsilon$:
--
--   1. at time zero $\varepsilon$ reports $\mu_{\varepsilon,0}(1)=\tfrac12$;
--   2. at time one her log-belief ratio is
--   $$\phi_{\varepsilon,1}=(\ell_1-\ell_0)\Bigl(2s_\kappa+\sum_{j=1}^3 s_{\varepsilon^{(j)}}\Bigr)+5\ell_0;$$
--   3. she reports $\mu_{\varepsilon,1}(1)=\tfrac{243}{371}$, i.e. $\phi_{\varepsilon,1}=3\ell_1+2\ell_0$ as in (19), if and only if $2s_\kappa+\sum_{j=1}^3 s_{\varepsilon^{(j)}}=3$;
--   4. consequently the history (19) occurs on $s$ if and only if $(s_\kappa,s_{\tau_1},\dots,s_{\tau_n})\in\Sigma$.
--
--   This is how agent $i$'s observation of the element agents turns into the integer constraints (20), the analogue of Fact 2 in the vertex-cover reduction.
--
--   **Formalization Note.** The belief $\mu_{\varepsilon,1}$ is computed by the revealed-belief dynamics on the network `xcNet X`, not assumed; $\phi=\log(\mu(1)/\mu(0))$ (`rLog`). The sum is over the three subsets containing $\varepsilon$, computed in $\mathbb N$ and cast to $\mathbb R$.
--
--   Differences from the source:
--   - reading: the history (19) of agent i → `Observed X s`, the element agents' reports 1/2 at time 0 and 243/371 at time 1; reason: 243/371 is the belief with log-ratio 3ℓ_1 + 2ℓ_0 = log(243/128), and the time-zero reports, also part of i's history, are 1/2 on every profile.
--   - reading: the displayed chain φ_ε,1 = λ_κ + Σ_j λ_ε(j) = … → only its final closed form; reason: the intermediate expressions are equal to it by definition of λ, ℓ⋆_b = 2ℓ_b.
--   - encoding: element agents with non-informative signals → signal probability 1/2 in both states; reason: a non-informative signal is one with equal laws in the two states.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 32, (19), (20) and the display before (20)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network

namespace BayesGroupHard.VertexCover.Supplement

open Finset

/-- (20), p. 32: in the Appendix B network, every element agent reports `µ_ε,0(1) = 1/2` at time
zero; at time one her log-belief ratio is `φ_ε,1 = (ℓ_1 - ℓ_0)(2 s_κ + Σ_j s_ε(j)) + 5 ℓ_0`;
she reports `243/371` (that is, `φ_ε,1 = 3ℓ_1 + 2ℓ_0`, (19)) iff `2 s_κ + Σ_j s_ε(j) = 3`; and
the history (19) holds iff the informative signals lie in `Σ`. -/
theorem eq_20 {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool) :
    (∀ e, report (xcNet X) 0 (epsilon e) s = 1 / 2) ∧
    (∀ e, rLog (xcNet X) 1 (epsilon e) s =
      (ellOne - ellZero) *
        ((2 * bit (s kappa) +
          ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) : ℕ) : ℝ) +
        5 * ellZero) ∧
    (∀ e, report (xcNet X) 1 (epsilon e) s = 243 / 371 ↔
      2 * bit (s kappa) + ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) = 3) ∧
    (Observed X s ↔ project s ∈ sigma X) := by sorry

end BayesGroupHard.VertexCover.Supplement
