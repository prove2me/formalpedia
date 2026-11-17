-- Prove2me | Theorems.Thm_BilatMatch_Supplement_theorem_B_11
-- name    : BilatMatch.Supplement.theorem_B_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:31:25.145229+00:00
-- url     : https://prove2.me/theorems/98132fd8-4e9c-4867-a860-66c2ab7a8922
-- title:
--   Theorem B.11 (Cap-Dependent Bilateral Bounds) — $F_S(\kappa)V_\alpha(F_B,F_S^\kappa)\ge\sum_\ell f_B(v_\ell)T^\kappa_\ell$ iff a cap-compatible family meets $T$
-- statement:
--   Fix $\alpha\ge0$, buyer values $v_1<\dots<v_n$, and an $\alpha$-weakly regular seller prior $F_S$ with finite support or regular interval support as in §3.2. Let targets $T^\kappa_\ell\ge0$ (one per initial seller cap $\kappa$ and buyer index $\ell$) increase with cap inclusion and vanish on zero-mass caps. The following are equivalent:
--
--   1. for every positive-mass cap $\kappa$ and every buyer prior $F_B$ with support $\{v_1,\dots,v_n\}$,
--   $$F_S(\kappa)\,V_\alpha(F_B,F^\kappa_S)\ \ge\ \sum_\ell f_B(v_\ell)\,T^\kappa_\ell ;$$
--   2. there is a cap-compatible family $z^\kappa$ with $\ell^\kappa_\alpha(v_\ell;z^\kappa)\ge T^\kappa_\ell$ for every cap $\kappa$ and every $\ell$.
--
--   Here $F^\kappa_S(A)=F_S(A\cap\kappa)/F_S(\kappa)$ and $\ell^\kappa_\alpha$ is the typewise contribution (5) under the unconditioned seller prior. This generalizes Theorem 3.5 from the targets $\beta\int_\kappa(v_\ell-c)_+dF_S$ to arbitrary monotone cap-dependent targets, and makes it an equivalence.
--
--   **Formalization Note** Caps are initial sets of the seller report domain, possibly empty, open or closed.
--
--   Differences from the source:
--   - reading: bilateral V_α(F_B, F^κ_S) → bilateral V_α with BIC/IIR at every real type and report (whole-line Valpha); reason: as in the published Theorem 3.5: for finite priors the support-restricted and whole-line values coincide (Lemma B.4(i))
--   - encoding: every buyer prior F_B with support {v_1, …, v_n} → ∑_ℓ w_ℓ δ_{v_ℓ} with all w_ℓ > 0, ∑ w_ℓ = 1; reason: the priors with exactly this support
--   - encoding: targets T^κ_ℓ ≥ 0, increasing with cap inclusion, vanishing on zero-mass caps → a function T κ ℓ constrained on caps of DS only; reason: only caps enter the statement
--   - encoding: α-weakly regular seller with finite or interval support (§3.2) → the published IsAlphaWeaklyRegular α F DS τα; reason: the base chunk's definition, as in Theorem 3.5
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), Theorem B.11, pp.37–38 (pdf pp.39–40); standing assumptions §3.2, p.10 (pdf p.12)

import Mathlib
import Definitions.Def_BilatMatch_sellerCost
import Definitions.Def_BilatMatch_massLagrangian
import Definitions.Def_BilatMatch_typewise
import Definitions.Def_BilatMatch_ValphaOn

open MeasureTheory

namespace BilatMatch.Supplement

open BilatMatch

/-- **Theorem B.11 (Cap-Dependent Bilateral Bounds).** Liu, Qin, Wang, *From Bilateral Trade to
Matching Markets: Sharp Gains from Trade*, arXiv:2609.30702 (held version, sha256 ff1490ad…),
Theorem B.11, pp.37–38 (pdf pp.39–40); standing assumptions of §3.2, p.10.

Fix `α ≥ 0`, buyer values `v_1 < ⋯ < v_n`, and an `α`-weakly regular seller prior `F_S` with finite
or interval support. Let `T^κ_ℓ ≥ 0` increase with cap inclusion and vanish on zero-mass caps. Then
the following are equivalent:
(i) for every positive-mass cap `κ` and every buyer prior `F_B` with support `{v_1, …, v_n}`,
    `F_S(κ) V_α(F_B, F^κ_S) ≥ ∑_ℓ f_B(v_ℓ) T^κ_ℓ`;
(ii) there is a cap-compatible family `z^κ` with `ℓ^κ_α(v_ℓ; z^κ) ≥ T^κ_ℓ` for every cap `κ` and every `ℓ`.

**Formalization Note** As in the published Theorem 3.5: buyer priors on the support are
`∑_ℓ w_ℓ δ_{v_ℓ}` with all `w_ℓ > 0`; caps are initial sets of the seller report domain `DS` (the
support, or `[c̲, c̄]`), possibly empty, open or closed; `F^κ_S` is `ProbabilityTheory.cond F κ`;
`V_α` is the whole-line bilateral `Valpha` and `F_S(κ)` multiplies it in `EReal`; `ℓ^κ_α` is
`typewise` (eq. (5)) with the unconditioned seller prior and buyer domain `{v_1, …, v_n}`. The targets
are a function `T κ ℓ` of the cap and the buyer index, constrained only on caps. -/
theorem theorem_B_11 (α : ℝ) (hα : 0 ≤ α) (F : Measure ℝ) (DS : Set ℝ) (τα : ℝ → ℝ)
    (hF : IsAlphaWeaklyRegular α F DS τα) {n : ℕ} (v : Fin n → ℝ) (hv : StrictMono v)
    (T : Set ℝ → Fin n → ℝ) (hTnn : ∀ κ, IsCap DS κ → ∀ ℓ, 0 ≤ T κ ℓ)
    (hTmono : ∀ κ κ', IsCap DS κ → IsCap DS κ' → κ ⊆ κ' → ∀ ℓ, T κ ℓ ≤ T κ' ℓ)
    (hTzero : ∀ κ, IsCap DS κ → F κ = 0 → ∀ ℓ, T κ ℓ = 0) :
    (∀ κ : Set ℝ, IsCap DS κ → 0 < F κ → ∀ w : Fin n → ℝ, (∀ ℓ, 0 < w ℓ) → ∑ ℓ, w ℓ = 1 →
      ((∑ ℓ, w ℓ * T κ ℓ : ℝ) : EReal) ≤
        (((F κ).toReal : ℝ) : EReal) *
          Valpha (bilateral (finiteLaw v w) (ProbabilityTheory.cond F κ)) α) ↔
    ∃ z : Set ℝ → ℝ → ℝ → ℝ, IsCapCompatible (Set.range v) DS z ∧
      ∀ κ : Set ℝ, IsCap DS κ → ∀ ℓ : Fin n,
        T κ ℓ ≤ typewise α (Set.range v) DS F (z κ) (v ℓ) := by sorry

end BilatMatch.Supplement
