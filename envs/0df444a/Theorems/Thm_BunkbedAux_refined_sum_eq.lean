-- Prove2me | Theorems.Thm_BunkbedAux_refined_sum_eq
-- name    : BunkbedAux.refined_sum_eq
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T01:18:58.324458+00:00
-- url     : https://prove2.me/theorems/fb3026fc-c626-442a-96e6-2edd74db7d87
-- title:
--   The refined model computes the same expectations
-- statement:
--   The refinement of the Wierman--Ziff pair state space splits each of the two pairs $(abc,\,a|b|c)$ and $(a|b|c,\,abc)$ into a $+$ and a $-$ variant, of weights $P_{ab|c}P_{ac|b}$ and $P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$. Hyperedge by hyperedge this is clearly harmless, since the two weights sum to the weight of the unsplit pair. This theorem upgrades that observation to whole configurations.
--
--   Let $\iota$ index the hyperedges. A *refined configuration* is a map $\Psi : \iota \to \Upsilon^2_{\mathrm{ext}}$, and it is **legal** when no entry is one of the two redundant copies of a split pair. Each refined configuration determines an ordinary pair configuration $\varphi = \texttt{toPair} \circ \Psi$, which is what fixes the realised graph. The claim is that for *every* function $g$ of the pair configuration,
--
--   $$\sum_{\Psi \text{ legal}} \Bigl(\prod_i \texttt{wt}(\Psi(i))\Bigr)\, g\bigl(\texttt{toPair} \circ \Psi\bigr) \;=\; \sum_{\varphi} \Bigl(\prod_i P(\varphi(i)_1)\,P(\varphi(i)_2)\Bigr)\, g(\varphi).$$
--
--   Taking $g$ to be a connectivity indicator shows that no probability whatsoever is changed by passing to the refined model; the refinement is pure bookkeeping.
--
--   **Mathematical role.** This is what makes the involution argument of Gladkov--Pak--Zimin legitimate. The involution lives on the *refined* configuration space — it has to, because it exchanges a sub-event of $(abc, a|b|c)$ of weight $P_{ab|c}P_{ac|b}$ with the pair $(ab|c, ac|b)$, and no such weight-preserving exchange exists before refining. This theorem is the statement that a cancellation established in the refined model is a cancellation of genuine Wierman--Ziff probabilities.
--
--   **Formalization note.** The proof groups refined configurations by the pair configuration they induce. Over a fixed $\varphi$ the fibre is a product of per-hyperedge fibres, so the sum of products factors as a product of sums; each per-hyperedge fibre then contributes exactly $P(\varphi(i)_1)P(\varphi(i)_2)$, which for the two split pairs is where the two variant weights recombine. Note the statement holds for an arbitrary finite index type and arbitrary $P$; no hypothesis that $P$ is a probability distribution is needed.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.3 (p. 4): the extended state space and Eq. [4], where the refinement is introduced and asserted not to change the model.

import Definitions.Def_BunkbedWZRefined
open Bunkbed.Hyper Finset

namespace BunkbedAux

/-- **The refined model computes the same expectations as the Wierman-Ziff model.** Summing any
function of the underlying pair configuration against the refined weights over all *legal*
refined configurations gives the same value as summing it against the ordinary product weights
over all pair configurations. So the refinement is measure-preserving at the level of whole
configurations, not merely hyperedge by hyperedge. -/
theorem refined_sum_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (P : WZ → ℚ)
    (g : (ι → WZ × WZ) → ℚ) :
    ∑ Ψ ∈ Finset.univ.filter (fun Ψ : ι → WZExt => ∀ i, WZExt.legal (Ψ i) = true),
        (∏ i, WZExt.wt P (Ψ i)) * g (fun i => WZExt.toPair (Ψ i))
      = ∑ φ : ι → WZ × WZ, (∏ i, P (φ i).1 * P (φ i).2) * g φ := by
  sorry

end BunkbedAux
