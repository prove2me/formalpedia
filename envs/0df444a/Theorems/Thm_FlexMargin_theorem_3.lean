-- Prove2me | Theorems.Thm_FlexMargin_theorem_3
-- name    : FlexMargin.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:46:23.216977+00:00
-- url     : https://prove2.me/theorems/37bd187b-5a42-40e5-896a-99f129f26a0c
-- title:
--   Theorem 3: the alternate long chain is worst-case optimal among long chains
-- statement:
--   Consider a balanced system with $n$ plants of unit capacity and $n$ products, of which $n/2$ are **high profit** products (margin $P_H$) and $n/2$ are **low profit** products (margin $P_L<P_H$).
--   Let $\mathcal{AL}$ be an alternate long chain and $\mathcal L_{HL}$ any long chain design on this system. Then for every part-wise independently symmetric uncertainty set $U$ (Definition 2.1) and every robust measure $R\in\Gamma$,
--
--   $$
--   R(\mathcal{AL},U)\ \ge\ R(\mathcal L_{HL},U).
--   $$
--
--   Here $R=R^f$ with $f(\mathcal A,d)=h\big(g(\mathcal A,d),\sum_{i\in S_L}d_i,\sum_{i\in S_H}d_i\big)$, $g$ the maximum profit (1) and $h$ strictly increasing in its first argument; examples are the worst-case profit and the worst-case profit loss. Among long chains, spreading high and low profit products alternately is therefore optimal for every such measure and every such uncertainty set.
--
--   **Formalization Note** $R$ is the infimum over $U$ in the extended reals.
--
--   Differences from the source:
--   - generalization: R^f(A,U) = min_{d∈U} f(A,d), with f continuous in d so that the minimum exists → R is the infimum in EReal over U (robustMeasure); no continuity of f, no compactness of U; reason: the EReal infimum equals the minimum whenever it exists, so the statement specializes to the source's
--   - encoding: §4 system: n plants and n products, C_j = 1, two categories S_L, S_H with margins P_L < P_H, |S_H| = |S_L| = n/2 → cat : Fin n → Fin 2 (0 low, 1 high), P = ![P_L, P_H], C ≡ 1, hypothesis #{cat = 1} = #{cat = 0}; reason: Lean indexing; same instances
--   - encoding: long chain designs; the alternate long chain AL (H and L products assigned alternately) → IsLongChain A: A is the long chain L with plants and products relabelled by permutations π, τ; IsAltLongChain: in addition consecutive products τ i, τ (i+1 mod n) have different categories; reason: designs vary, margins are fixed (Reading 1): the only reading under which two long chains are compared on one system with one U; same designs
--   - encoding: h(x, Σd_{s_1}, Σd_{s_2}) with s_1 = S_L, s_2 = S_H → h : ℝ → (Fin 2 → ℝ) → ℝ applied to g and the vector (Σ_{S_L} d, Σ_{S_H} d); reason: Lean currying; same functions
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §4.1, Theorem 3, p. 21

import Mathlib
import Definitions.Def_FlexMargin_marginMeasure
import Definitions.Def_FlexMargin_IsMonotonicInProfit
import Definitions.Def_FlexMargin_robustMeasure
import Definitions.Def_FlexMargin_IsPartwiseSymm
import Definitions.Def_FlexMargin_IsLongChain
import Definitions.Def_FlexMargin_IsAltLongChain

open Finset

namespace FlexMargin

/-- **Theorem 3: the alternate long chain is worst-case optimal among long chains.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §4.1, Theorem 3, p. 21: "Let LHL be a long chain design with equal number of high profit
products and low profit products. Then, for any part-wise independently symmetric uncertainty set U
and any robust measure R ∈ Γ, we have R(AL,U) ≥ R(LHL,U)."

The system of §4 (p. 19): `n` plants and `n` products, unit capacities `C ≡ 1`, two margins `P_L < P_H`,
product categories `cat : Fin n → Fin 2` (`0` low, `1` high) with as many high as low profit products.
For every alternate long chain `AL` (`FlexMargin.IsAltLongChain`), every long chain `LHL`
(`FlexMargin.IsLongChain`), every part-wise independently symmetric `U` (`FlexMargin.IsPartwiseSymm`,
Definition 2.1), and every `h` strictly increasing in its first argument (`R = R^f ∈ Γ` with
`f(A, d) = h(g(A, d), (Σ_{S_L} d, Σ_{S_H} d))`, `FlexMargin.marginMeasure`):
`R(LHL, U) ≤ R(AL, U)` (`FlexMargin.robustMeasure`).

**Formalization Note.** (a) `R` is the infimum in `EReal`; it equals the paper's minimum whenever
that exists, and `f` is not assumed continuous. (b) Plants and products are `Fin n`; a long chain is
the long chain `ℒ` with plants and products relabelled; the margins of the products are the same for
`AL` and `LHL`. (c) `h`'s second argument is the vector `(Σ_{i ∈ S_L} d_i, Σ_{i ∈ S_H} d_i)`; `g` is the
LP (1) with `C ≡ 1` and margins `![P_L, P_H] (cat i)`. (d) No sign condition on the margins. -/
theorem theorem_3 (n : ℕ) (PL PH : ℝ) (hP : PL < PH) (cat : Fin n → Fin 2)
    (hbal : (univ.filter (fun i => cat i = 1)).card = (univ.filter (fun i => cat i = 0)).card)
    (AL LHL : Finset (Fin n × Fin n)) (hAL : IsAltLongChain cat AL) (hLHL : IsLongChain LHL)
    (U : Set (Fin n → ℝ)) (hU : IsPartwiseSymm cat U)
    (h : ℝ → (Fin 2 → ℝ) → ℝ) (hh : IsMonotonicInProfit h) :
    robustMeasure (marginMeasure (fun _ => (1 : ℝ)) ![PL, PH] cat h) LHL U ≤
      robustMeasure (marginMeasure (fun _ => (1 : ℝ)) ![PL, PH] cat h) AL U := by sorry

end FlexMargin
