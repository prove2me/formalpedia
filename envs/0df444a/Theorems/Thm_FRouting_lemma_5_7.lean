-- Prove2me | Theorems.Thm_FRouting_lemma_5_7
-- name    : FRouting.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:29.893142+00:00
-- url     : https://prove2.me/theorems/bd9923f2-5739-49f0-8721-87e3b8b5e709
-- title:
--   Lemma 5.7 — reduction from $L_f$ to $\mathrm{coQSD}_{\alpha,\beta}$
-- statement:
--   There are universal $\varepsilon_0>0$, a polynomial $p_0$ and constants $0\le\alpha<\beta^2\le1$, $\beta\ge0$, such that for all $d,T$ as in Definition 3.6, every family $f$ and every $T$-uniform strategy that is $(1-\varepsilon)$-correct on every input with $0\le\varepsilon\le\varepsilon_0$, there is a deterministic many-one reduction $R$ from $L_f$ to $\mathrm{coQSD}_{\alpha,\beta}$ computable in time
--   $$p_0\big(T(m/2)+\lceil\log_2 d(m/2)\rceil\big)$$
--   on inputs of length $m$.
--
--   The instance is the pair of circuits preparing $\rho^{xy}_{\bar QA}$ and $\rho^{xy}_{\bar Q}\otimes\rho^{xy}_A$.
--
--   Differences from the source:
--   - reading: a "description of a quantum channel", with no gate set (p.4) → circuits over X_d, Z_d, F_d, T_d, SUM_d, with ancillas and traced wires; reason: the paper fixes no model; at d = 2 this is its Clifford+T set, and Solovay–Kitaev covers other finite universal sets at d = 2
--   - reading: T(n) and d(n) on input length n = |x| → T(m/2) and d(m/2) on input length m = |x ∘ y|, floored; reason: the class counts length m = 2n; as T and d are nondecreasing and the bound monotone, this is at least as strong as the literal T(m)
--   - reading: time-constructible, not defined in the paper → a machine prints g(n) in binary from 1ⁿ within C·g(n) + C steps; reason: the standard notion; it is only a hypothesis on T and d
--   - generalization: post-communication generators Gen^post, unrestricted (Definition 3.6) → arbitrary post-communication channels, with no machine; reason: the proof never runs them; machine-generated decoders are a special case
--   - encoding: time, size and width at most T(n) → at most max(1, T(n)); reason: a machine takes at least one step and a circuit on Q has a wire, so T(0) = 0 (allowed by T(n) ≥ n, e.g. T(n) = n²) could not be met; the bound changes only where T(n) = 0
--   - encoding: machine inputs 1ⁿ and (1ⁿ, x), and printed partitions → the strings 1ⁿ and 1ⁿ0x, and the partition widths in unary before the circuit; reason: one fixed pairing; it changes step counts by a linear term only, within T(n) ≥ n up to the machine
--   - encoding: log d → Nat.clog 2 d; reason: the ceiling of the base-2 logarithm, a natural number; same up to an additive 1
--   - encoding: 0 ≤ α < β² ≤ 1 → the same, and 0 ≤ β; reason: Definition 5.5 has 0 ≤ α < β ≤ 1, and the proof has β = 1/2 − √(2ε₀) > 0
--   - reading: pairs of circuits, with the map (x, y) ↦ (1ⁿ, C₀, C₁) (p.22) → instances over one qudit dimension with free padding; reason: the circuits of the map are d-dimensional, and 1ⁿ needs room in the string
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 5.7, p.21; proof, pp.21–22

import Definitions.Def_FRouting_QSD
import Definitions.Def_FRouting_UniformStrategy

set_option autoImplicit false

namespace FRouting

/-- **Lemma 5.7 (the reduction).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 5.7, p.21: "There are a constant ε₀ > 0 and a universal
polynomial p₀ such that the following holds. Suppose that an f-routing strategy is a T-uniform strategy
that is (1 − ε)-correct on every input, where 0 ≤ ε ≤ ε₀. Then, for some universal constants
0 ≤ α < β² ≤ 1, there is a deterministic many-one reduction R computable in time
T_reduction(n) := p₀(T + log d) from L_f to coQSD_{α,β}."

**Formalization Note** `ε₀, p₀, α, β` come before `d, T, f, S`: they are universal, and the proof
fixes `α, β` from `ε₀` (p.22). `0 ≤ β` is part of the constants of Definition 5.5. On input length
`m` the time is `p₀(T(m/2) + ⌈log₂ d(m/2)⌉)`, since `T` and `d` are functions of `n = |x|` and
`m = 2n`. The reduction is defined on all strings: Yes to Yes, and No to No, odd lengths included. -/
theorem lemma_5_7 :
    ∃ (ε₀ : ℝ) (p₀ : Polynomial ℕ) (α β : ℝ),
      0 < ε₀ ∧ 0 ≤ α ∧ α < β ^ 2 ∧ β ^ 2 ≤ 1 ∧ 0 ≤ β ∧
      ∀ (d T : ℕ → ℕ), IsTimeConstructible d → IsTimeConstructible T → Monotone d → Monotone T →
        (∀ n, 2 ≤ d n) → (∀ n, n ≤ T n) →
        ∀ (f : ∀ n, (Fin n → Bool) → (Fin n → Bool) → Bool) (S : UniformStrategy d T) (ε : ℝ),
          0 ≤ ε → ε ≤ ε₀ → (∀ n x y, (S.toRouting n).IsCorrectOn (f n) ε x y) →
          ∃ (M : StrMachine) (R : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str),
            (∀ w, PrintsInTime M w (R w)
              (p₀.eval (T (w.length / 2) + Nat.clog 2 (d (w.length / 2))))) ∧
            (∀ w ∈ (languageOf f).Yes, R w ∈ (coQSD α β).Yes) ∧
            (∀ w ∈ (languageOf f).No, R w ∈ (coQSD α β).No) := by sorry

end FRouting
