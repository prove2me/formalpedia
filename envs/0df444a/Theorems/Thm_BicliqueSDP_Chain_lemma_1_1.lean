-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_lemma_1_1
-- name    : BicliqueSDP.Chain.lemma_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:26.359913+00:00
-- url     : https://prove2.me/theorems/130a44a2-ed2c-41e5-99f6-192e0ed289b6
-- title:
--   Lemma 1.1, p. 2 — ¼α_bal = ½√g_bal = h_bal ≤ h ≤ ½√g ≤ ¼α, and the equality cases
-- statement:
--   Let $G=(V_1\cup V_2,E)$ be a bipartite graph, and let $\alpha$, $g$, $h$ and their balanced analogues $\alpha_{\mathrm{bal}}$, $g_{\mathrm{bal}}$, $h_{\mathrm{bal}}$ be the maxima of $|A|+|B|$, $|A|\cdot|B|$ and $|A|\cdot|B|/(|A|+|B|)$ over all (respectively, all balanced) bipartite biindependent pairs $(A,B)$. Then
--
--   $$\tfrac14\alpha_{\mathrm{bal}}(G)=\tfrac12\sqrt{g_{\mathrm{bal}}(G)}=h_{\mathrm{bal}}(G)\le h(G)\le\tfrac12\sqrt{g(G)}\le\tfrac14\alpha(G),\tag{3}$$
--
--   $$h(G)=\tfrac14\alpha(G)\iff\tfrac12\sqrt{g(G)}=\tfrac14\alpha(G)\iff\alpha(G)=\alpha_{\mathrm{bal}}(G).\tag{4}$$
--
--   The chain (3) gives the first inequality of Proposition 1.2, $h(G)\le\frac12\sqrt{g(G)}$, and (4) characterises when the combinatorial bounds are tight.
--
--   **Formalization Note** The chained equivalences (4) are stated as two biconditionals.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 2, Lemma 1.1, relations (3) and (4)

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- Lemma 1.1 (p. 2): relations (3) and (4). -/
theorem lemma_1_1 {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    ((1 / 4) * alphaBal E = (1 / 2) * Real.sqrt (gBal E) ∧
      (1 / 2) * Real.sqrt (gBal E) = hBal E ∧ hBal E ≤ h E ∧
      h E ≤ (1 / 2) * Real.sqrt (g E) ∧ (1 / 2) * Real.sqrt (g E) ≤ (1 / 4) * alpha E) ∧
    ((h E = (1 / 4) * alpha E ↔ (1 / 2) * Real.sqrt (g E) = (1 / 4) * alpha E) ∧
      ((1 / 2) * Real.sqrt (g E) = (1 / 4) * alpha E ↔ alpha E = alphaBal E)) := by sorry

end BicliqueSDP.Chain
