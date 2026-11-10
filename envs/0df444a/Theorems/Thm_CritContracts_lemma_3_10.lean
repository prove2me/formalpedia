-- Prove2me | Theorems.Thm_CritContracts_lemma_3_10
-- name    : CritContracts.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:39.004311+00:00
-- url     : https://prove2.me/theorems/873da475-42b5-4c67-b85f-b814cbb66592
-- title:
--   Lemma 3.10 — greatest best responses are monotone in $t$ and $S_{-i}$; $\alpha\le\beta\Rightarrow S^+(\alpha)\subseteq S^+(\beta)$
-- statement:
--   Let $f$ be monotone and supermodular. For every agent $i$, the greatest best response $\mathrm{BR}^+_i(t,S_{-i})$ is nondecreasing both in the share $t\in[0,1]$ and in the others' actions $S_{-i}$:
--
--   1. if $0\le t\le t'\le1$ then $\mathrm{BR}^+_i(t,S_{-i})\subseteq\mathrm{BR}^+_i(t',S_{-i})$;
--   2. if $S_{-i}\subseteq S'_{-i}$ then $\mathrm{BR}^+_i(t,S_{-i})\subseteq\mathrm{BR}^+_i(t,S'_{-i})$.
--
--   Consequently, if $\alpha,\beta\in[0,1]^n$ and $\alpha\le\beta$ coordinate-wise, then
--   $$S^+(\alpha)\subseteq S^+(\beta).$$
--
--   This monotonicity underlies the hidden-payment representation of §3.3 and is the step "by Topkis' monotonicity theorem, $S\subseteq S'$" of the proof of Theorem 3.5.
--
--   **Formalization Note** Greatest best responses and greatest equilibria are predicates; the statement applies to any objects satisfying them.
--
--   Differences from the source:
--
--   - reading: f the reward of §3 (normalized, monotone, supermodular, [0,1]-valued) → f monotone and supermodular; reason: §3 studies supermodular rewards and p.10 restricts to monotone rewards throughout; normalization and the [0,1] range are not used
--   - encoding: BR⁺ᵢ(t, S₋ᵢ) and S⁺(α) as functions → predicates IsGreatestBR and IsGreatestNE; the inclusion holds for any objects satisfying them; reason: avoids junk values; they exist by Lemma 3.3 and Appendix D.1
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Lemma 3.10, p.17 (PDF p.18); proof in Appendix D.1, p.48 (PDF p.49)

import Mathlib
import Definitions.Def_CritContracts_Model
import Definitions.Def_CritContracts_IsSupermodular
import Definitions.Def_CritContracts_IsGreatestBR

set_option autoImplicit false

namespace CritContracts

open Model

/-- **Lemma 3.10** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*,
STOC 2027 submission (manuscript sha256 430be35c…), §3.3.1, p.17, PDF p.18): for monotone supermodular `f` and every agent
`i`, the greatest best response `BR⁺ᵢ(t, S₋ᵢ)` is nondecreasing both in the share `t ∈ [0,1]` and
in the others' actions `S₋ᵢ`. Consequently, if `α, β ∈ [0,1]ⁿ` and `α ≤ β` coordinate-wise, then
`S⁺(α) ⊆ S⁺(β)`.

**Formalization Note** `BR⁺ᵢ` and `S⁺` are predicates (`IsGreatestBR`, `IsGreatestNE`): the
statement holds for any greatest best responses and greatest equilibria (their existence is
Lemma 3.3 and the proof of Lemma 3.10 on p.48). Monotonicity "in `t`" is stated at fixed `S₋ᵢ`
and monotonicity "in `S₋ᵢ`" at fixed `t`. -/
theorem lemma_3_10 {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
    (M : Model ι T) (hmono : IsMonotone M.f) (hsup : IsSupermodular M.f) :
    (∀ (i : ι) (t t' : ℝ) (X D D' : Finset T), 0 ≤ t → t ≤ t' → t' ≤ 1 →
        (∀ j ∈ X, M.owner j ≠ i) →
        M.IsGreatestBR i t X D → M.IsGreatestBR i t' X D' → D ⊆ D') ∧
    (∀ (i : ι) (t : ℝ) (X X' D D' : Finset T), 0 ≤ t → t ≤ 1 →
        (∀ j ∈ X', M.owner j ≠ i) → X ⊆ X' →
        M.IsGreatestBR i t X D → M.IsGreatestBR i t X' D' → D ⊆ D') ∧
    (∀ (α β : ι → ℝ) (G G' : Finset T), IsContract α → IsContract β → (∀ i, α i ≤ β i) →
        M.IsGreatestNE α G → M.IsGreatestNE β G' → G ⊆ G') := by sorry

end CritContracts
