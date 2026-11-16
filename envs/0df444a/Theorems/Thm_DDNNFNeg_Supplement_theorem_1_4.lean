-- Prove2me | Theorems.Thm_DDNNFNeg_Supplement_theorem_1_4
-- name    : DDNNFNeg.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:49:45.986323+00:00
-- url     : https://prove2.me/theorems/d022e02f-8664-4016-bdec-24bbf31eee2e
-- title:
--   Theorem 1.4 (= Corollary 8.8) — a UFA of size $s$ whose fixed-length complement needs CFG size $2^{\Omega(\log^2 s)}$
-- statement:
--   There is a constant $c > 0$ such that for infinitely many $s \in \mathbb N$ there exist $n \in \mathbb N$ and a **nonempty** language $L \subseteq \{0,1\}^n$ (all words of $L$ have length exactly $n$) with the following properties.
--
--   1. $L$ is decided by an **unambiguous finite automaton** (UFA) with exactly $s$ states and a single initial state.
--   2. Every context-free grammar $G$ generating the complement $\overline L = \{0,1\}^n \setminus L$ has size
--   $$|G| = \sum_{(S \to T) \in P} |T| \ \ge\ 2^{c \log^2 s}.$$
--
--   The bound holds for all context-free grammars, ambiguous or not. It improves the Göös–Kiefer–Yuan separation for complementing UFAs from NFA size to CFG size, and answers the question of Mengel and Vinall-Smeeth on complementing unambiguous grammars for finite languages.
--
--   **Formalization Note** The constant $c$ is fixed before "for infinitely many $s$" (for every $S$ there is $s \ge S$); $\log$ is the natural logarithm. The complement is taken inside $\{0,1\}^n$, not $\{0,1\}^*$. $L$ is required to be nonempty, as the proof on p.21 states; a UFA for a nonempty $L \subseteq \{0,1\}^n$ has at least $n+1$ states, so $n < s$.
--
--   Differences from the source:
--   - reading: size 2^{Ω(log²(s))}, for infinitely many s → a constant c > 0 fixed first, then ∀ S ∃ s ≥ S with every CFG size ≥ 2^{c·(ln s)²}; reason: standard reading of asymptotic notation; the base of the logarithm only rescales c
--   - encoding: UFA (Σ, Q, q0, F, δ) of size s (Definition 8.4) → Mathlib NFA over Bool with state type Fin s and start set {q₀}; unambiguity counts accepting state sequences; reason: the same automata; exactly s states
--   - encoding: CFG (N, N0, Σ, P) with N finite (Definition 8.6) → Mathlib ContextFreeGrammar Bool (finite rule set, nonterminal type in Type, not required finite); reason: nonterminals occurring in no rule change neither the language nor the size, so the grammars and sizes are the same
--   - reading: L ⊆ {0,1}^n decided by a UFA of size s (nonemptiness of L not written in the theorem) → ∃ w, w ∈ L, together with ∀ w ∈ L, w.length = n; reason: the literal statement is degenerate: L = ∅ (a UFA with no accept state) and a huge n meet it trivially, since every CFG for {0,1}^n has size tending to infinity with n; the proof on p.21 states that L is nonempty (whence s ≥ n + 1), so this is the statement the paper proves
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 1.4, p.5 (restated as Corollary 8.8 and proved on p.21)

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_IsUFAOfSize
import Definitions.Def_DDNNFNeg_Supplement_cfgSize

namespace DDNNFNeg.Supplement

/-- **Theorem 1.4** (= Corollary 8.8) (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.5; restated and proved p.21): for infinitely many
`s ∈ ℕ`, there exist `n ∈ ℕ` and a language `L ⊆ {0,1}^n` decided by a UFA of size `s` such
that any CFG generating `L̄ = {0,1}^n \ L` has size `2^{Ω(log² s)}`.

**Formalization Note** The constant `c > 0` of `Ω` is fixed before "for infinitely many `s`"
(`∀ S, ∃ s ≥ S`); `log` is the natural logarithm (another base only rescales `c`). `L` is a set of
words of length exactly `n`, and its complement is taken inside `{0,1}^n`. `L` is nonempty, as
the proof on p.21 states ("Finally, L is nonempty"); without it the literal statement is met
trivially by `L = ∅` (a UFA with no accept state) and a huge `n`, since every CFG for `{0,1}^n`
has size tending to infinity with `n`. With `L` nonempty, a UFA for `L` has at least `n + 1`
states (p.21), so `n < s`. The UFA has exactly
`s` states and one initial state. The lower bound applies to every CFG (ambiguous or not) whose
language is exactly `L̄`; grammar size is the total length of right-hand sides. Grammars have
nonterminal types in `Type` (Mathlib's `ContextFreeGrammar`). -/
theorem theorem_1_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ S : ℕ, ∃ s ≥ S, ∃ n : ℕ, ∃ L : Language Bool,
      (∃ w, w ∈ L) ∧ (∀ w ∈ L, w.length = n) ∧ IsUFAOfSize L s ∧
      ∀ g : ContextFreeGrammar Bool,
        g.language = ({w : List Bool | w.length = n ∧ w ∉ L} : Language Bool) →
        (2 : ℝ) ^ (c * Real.log s ^ 2) ≤ (cfgSize g : ℝ) := by sorry

end DDNNFNeg.Supplement
