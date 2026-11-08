-- Prove2me | Theorems.Thm_FRouting_theorem_5_2
-- name    : FRouting.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:28.02985+00:00
-- url     : https://prove2.me/theorems/48865ce8-b66a-4aa3-9200-5e504f60378a
-- title:
--   Theorem 5.2, with Theorem 1.3 as the $d=2$ clause — a uniform attack puts $f$ in time-bounded QSZK
-- statement:
--   There are a universal polynomial $p$, a constant $c\ge1$ and a constant $\varepsilon_0>0$ with the following property. Let $d,T:\mathbb N\to\mathbb N$ be time-constructible and nondecreasing, with $d(n)\ge2$ and $T(n)\ge n$. If a $T$-uniform $f$-routing strategy is $(1-\varepsilon)$-correct on every input, where $0\le\varepsilon\le\varepsilon_0$, then
--
--   1. $f\in\mathrm{QSZK}(T_{\rm attack})$, where $T_{\rm attack}(n)=p(T(n)+\log d(n))$;
--   2. if $d=2$ for every $n$, then $f\in\mathrm{QSZK}(T^c)$.
--
--   The class is for the language $L_f=\{x\circ y\mid f_n(x,y)=1\}$. The result turns a successful attack on the protocol into a bound on the complexity of $f$, for arbitrary quantum channels within the resource bound.
--
--   Differences from the source:
--   - reading: a "description of a quantum channel", with no gate set (p.4) → circuits over X_d, Z_d, F_d, T_d, SUM_d, with ancillas and traced wires; reason: the paper fixes no model; at d = 2 this is its Clifford+T set, and Solovay–Kitaev covers other finite universal sets at d = 2
--   - reading: "Quantum Statistical Zero-Knowledge proof", cited from [Wat02; Wat09] → InQSZK: qubit-circuit protocols, unrestricted provers, completeness ≥ 1 − μ, soundness ≤ μ, μ negligible and ≤ 1/3; reason: the paper does not define the proof; these errors imply both the 2/3–1/3 and the negligible conventions
--   - reading: "every verifier Ver* ... has a simulator" → cheating verifiers with auxiliary input, on the honest protocol's message qubits and number of rounds; the honest prover fixed first; trace distance tested on any finite reference; reason: the strong reading of [Wat09]; trivial auxiliary and reference recover the weaker one; a message the honest prover never reads, or a round it never answers, changes nothing
--   - reading: simulator time poly(T(n) + S(n)) → one polynomial r per problem, and a constant C per verifier: C · r(B + S); reason: a per-verifier polynomial would be weaker; a machine-dependent constant is unavoidable with exact step counts
--   - reading: T(n) and d(n) on input length n = |x| → T(m/2) and d(m/2) on input length m = |x ∘ y|, floored; reason: the class counts length m = 2n; as T and d are nondecreasing and the bound monotone, this is at least as strong as the literal T(m)
--   - reading: time-constructible, not defined in the paper → a machine prints g(n) in binary from 1ⁿ within C·g(n) + C steps; reason: the standard notion; it is only a hypothesis on T and d
--   - generalization: post-communication generators Gen^post, unrestricted (Definition 3.6) → arbitrary post-communication channels, with no machine; reason: the proof never runs them; machine-generated decoders are a special case
--   - encoding: time, size and width at most T(n) for the generators, and time at most T_attack(n) or T(n)^c for the class's verifiers → at most max(1, T(n)), and max(1, ·) of the class's bound; reason: a machine takes at least one step and a circuit on Q has a wire, so T(0) = 0 (allowed by T(n) ≥ n, e.g. T(n) = n²) could not be met; the bound changes only where T(n) = 0; likewise a class bound of 0 (T(0)^c = 0) could be met by no verifier, so the literal class would be empty there
--   - encoding: machine inputs 1ⁿ and (1ⁿ, x), and printed partitions → the strings 1ⁿ and 1ⁿ0x, and the partition widths in unary before the circuit; reason: one fixed pairing; it changes step counts by a linear term only, within T(n) ≥ n up to the machine
--   - encoding: log d → Nat.clog 2 d; reason: the ceiling of the base-2 logarithm, a natural number; same up to an additive 1
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 5.2, p.20; Theorem 1.3, p.5

import Definitions.Def_FRouting_InQSZK
import Definitions.Def_FRouting_UniformStrategy

set_option autoImplicit false

namespace FRouting

/-- **Theorem 5.2, with Theorem 1.3 as its `d = 2` clause (the goal).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 5.2, p.20: "There
are a universal polynomial p and a constant ε₀ > 0 with the following property. If a T-uniform
f-routing strategy is (1 − ε)-correct on every input, where 0 ≤ ε ≤ ε₀, then f ∈ QSZK(T_attack), where
T_attack(n) := p(T(n) + log d(n))." Theorem 1.3, p.5: "There exist universal constants ε₀ > 0 and c ≥ 1
such that, if a T-uniform f-routing strategy is correct with probability ≥ (1 − ε) on all inputs
x, y ∈ {0,1}ⁿ for some ε ≤ ε₀, then f ∈ QSZK(T^c)."

**Formalization Note** `p, c, ε₀` come before `d, T, f, S`. Neither printed conclusion literally gives
the other (`p(T + 1) ≤ T^c` needs `T ≥ 2`), so both are clauses, with one `ε₀`. `ε` is one number for
all `n`. On input length `m` of `L_f` the bound is at `n = m/2`: `T` and `d` are functions of
`n = |x|`, and `|x ∘ y| = 2n`; since `T`, `d` are nondecreasing this is at least as strong as the bound
at `m`. `log` is `Nat.clog 2`. -/
theorem theorem_5_2 :
    ∃ (p : Polynomial ℕ) (c : ℕ) (ε₀ : ℝ), 1 ≤ c ∧ 0 < ε₀ ∧
      ∀ (d T : ℕ → ℕ), IsTimeConstructible d → IsTimeConstructible T → Monotone d → Monotone T →
        (∀ n, 2 ≤ d n) → (∀ n, n ≤ T n) →
        ∀ (f : ∀ n, (Fin n → Bool) → (Fin n → Bool) → Bool) (S : UniformStrategy d T) (ε : ℝ),
          0 ≤ ε → ε ≤ ε₀ → (∀ n x y, (S.toRouting n).IsCorrectOn (f n) ε x y) →
          InQSZK (languageOf f) (fun m => p.eval (T (m / 2) + Nat.clog 2 (d (m / 2)))) ∧
          ((∀ n, d n = 2) → InQSZK (languageOf f) (fun m => T (m / 2) ^ c)) := by sorry

end FRouting
