-- Prove2me | Theorems.Thm_FlexMargin_proposition_1
-- name    : FlexMargin.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:41:42.687638+00:00
-- url     : https://prove2.me/theorems/27e86b8e-d648-400c-8ff6-cbfaa818b47c
-- title:
--   Proposition 1: the alternate long chain maximizes the DMGI among long chains
-- statement:
--   Consider a balanced system with $n$ plants of unit capacity and $n$ products, of which $n/2$ are **high profit** products (margin $P_H$) and $n/2$ are **low profit** products (margin $P_L<P_H$).
--   Let $\mathcal{AL}$ be an alternate long chain and $\mathcal L_{HL}$ any long chain design on this system. Then for every parameter set $K\in Q$,
--
--   $$
--   \delta^K(\mathcal{AL})\ \ge\ \delta^K(\mathcal L_{HL}),
--   $$
--
--   where $\delta^K$ is the DMGI (5). Together with Theorem 2(a) this yields Theorem 3.
--
--   Differences from the source:
--   - encoding: §4 system: n plants and n products, C_j = 1, two categories S_L, S_H with margins P_L < P_H, |S_H| = |S_L| = n/2 → cat : Fin n → Fin 2 (0 low, 1 high), P = ![P_L, P_H], C ≡ 1, hypothesis #{cat = 1} = #{cat = 0}; reason: Lean indexing; same instances
--   - encoding: long chain designs; the alternate long chain AL (H and L products assigned alternately) → IsLongChain A: A is the long chain L with plants and products relabelled by permutations π, τ; IsAltLongChain: in addition consecutive products τ i, τ (i+1 mod n) have different categories; reason: designs vary, margins are fixed (Reading 1): the only reading under which two long chains are compared on one system with one U; same designs
--   - encoding: parameter set K = {k_tr : t = 1..T, r = 0..t−1} and binary w_itr → K : (t : Fin T) → Fin (t+1) → ℕ (K t r is k_{t+1,r}); w as a level map w i ≤ cat i + 1; reason: Lean indexing; one level per product is exactly the w-constraints of (4)
--   - reading: (4)/(5) list y_i + z_j ≥ p_i and the w-constraints, not z_j ≥ 0 → z ≥ 0 is a constraint of dmgi / dmgi5; reason: (4) is defined from dual feasibility of (3), which has z ≥ 0 (p. 17), and the proofs of Proposition 3 (p. 41) and Lemma 2 (p. 44) use it; without it a plant with no arcs makes (4) unbounded below
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §4.1, Proposition 1, p. 22

import Mathlib
import Definitions.Def_FlexMargin_IsLongChain
import Definitions.Def_FlexMargin_IsAltLongChain
import Definitions.Def_FlexMargin_InQ
import Definitions.Def_FlexMargin_dmgi5

open Finset

namespace FlexMargin

/-- **Proposition 1: the alternate long chain has the largest DMGI among long chains.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §4.1, Proposition 1, p. 22: "Let LHL be a long chain design with equal number of high profit
products and low profit products. Then, δK(AL) ≥ δK(LHL) for any parameter set K ∈ Q."

The system of §4 (p. 19): \`n\` plants and \`n\` products (\`Fin n\`, 0-based), unit capacities, two
categories given by \`cat : Fin n → Fin 2\` (\`0\`: low margin \`P_L\`, \`1\`: high margin \`P_H\`, \`P_L < P_H\`),
with as many high as low profit products; the margins are \`P = ![P_L, P_H]\`.
`δ^K` is problem (5) (`FlexMargin.dmgi5`). Every alternate long chain `AL` and every long chain `LHL`
on this system are compared.

**Formalization Note.** No sign condition on the margins (the paper states none); for
`P_L < 0` low products impose no constraint in (5) and the comparison still holds. -/
theorem proposition_1 (n : ℕ) (PL PH : ℝ) (hP : PL < PH) (cat : Fin n → Fin 2)
    (hbal : (univ.filter (fun i => cat i = 1)).card = (univ.filter (fun i => cat i = 0)).card)
    (AL LHL : Finset (Fin n × Fin n)) (hAL : IsAltLongChain cat AL) (hLHL : IsLongChain LHL)
    (K : (t : Fin 2) → Fin (t.val + 1) → ℕ) (hK : InQ cat K) :
    dmgi5 ![PL, PH] cat LHL K ≤ dmgi5 ![PL, PH] cat AL K := by sorry

end FlexMargin
