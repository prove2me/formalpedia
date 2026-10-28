-- Prove2me | Theorems.Thm_CrossSell_Pricing_eq_6
-- name    : CrossSell.Pricing.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:09.974797+00:00
-- url     : https://prove2.me/theorems/44e4ba28-80f5-4bd0-8749-836b2716640a
-- title:
--   Eq. (6), p. 12 — the profit (5) regrouped by stage-1 outcome: Π = Σ_{i∈S+} d_i·((p_i − c_i) + t_i), p_0 − c_0 = 0
-- statement:
--   In the sequential multinomial logit model (main offer set $S$, $S^+ = S \cup \{0\}$, secondary sets $T_i$, utilities $u_i, v_{il}$, costs $c_i, s_l$), the total expected profit (5) can be written as a sum over the first-stage outcomes. For all main prices $\mathbf p$ and secondary prices $\mathbf r$,
--   $$\Pi(S,\mathbf T,\mathbf p,\mathbf r) = \sum_{i\in S^+}\frac{\exp(u_i - p_i)}{1 + \sum_{j\in S}\exp(u_j - p_j)}\left((p_i - c_i) + \sum_{l\in T_i}\frac{(r_l - s_l)\exp(v_{il} - r_l)}{1 + \sum_{k\in T_i}\exp(v_{ik} - r_k)}\right),$$
--   where for the no-purchase option $i = 0$ the margin is $p_0 - c_0 = 0$ and the weight is $\exp(u_0 - p_0) = 1$ (the outside utility is normalized to $0$), so that the weight of $i = 0$ is $d_0(S,\mathbf p)$.
--
--   Each consumer segment $i \in S^+$ contributes its main-product margin plus the secondary profit $t_i(\mathbf r)$ of Definition 1, weighted by its share $d_i(S,\mathbf p)$. This is the form of the pricing problem from which the paper's Theorem 1 starts.
--
--   **Formalization Note.** The weight $d_i$ is `mainProb S u p i` on `Option ι`, with `mainProb … none` $= 1/(1 + \sum_{j\in S}\exp(u_j - p_j))$, and the margin is `mainMargin c p i` with value $0$ at `none`.
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 12, eq. (6)

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem eq_6 {ι κ : Type*} (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) :
    profit S T u c s v p r =
      ∑ i ∈ S.insertNone, mainProb S u p i * (mainMargin c p i + secProfit T s v r i) := by sorry

end CrossSell.Pricing
