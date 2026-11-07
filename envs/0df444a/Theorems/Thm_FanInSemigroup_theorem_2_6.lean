-- Prove2me | Theorems.Thm_FanInSemigroup_theorem_2_6
-- name    : FanInSemigroup.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:10.336201+00:00
-- url     : https://prove2.me/theorems/4b5ec9fa-4c9c-44cb-b01b-036e0c857d33
-- title:
--   Theorem 2.6 — rs machines are simulated in size $O(n^3)$ and constant depth
-- statement:
--   Let $M$ be an rs machine with $m$ flipflops over an alphabet $\Sigma$, and let $\Sigma\to\{0,1\}^b$ be an injective code with $b\ge 1$. Then there are constants $D,C$ such that for every $n\ge 1$ there is a circuit on $nb$ inputs of depth at most $D$ and size at most
--
--   $$
--   C\,n^{3}
--   $$
--
--   which, on the code of every word $w$ of length $n$, outputs
--
--   1. the state $F^k_i$ of every flipflop $k$ after $i$ letters, for every $1\le i\le n$, and
--   2. a bit telling whether $M$ accepts $w$.
--
--   This is the constant-depth upper bound. Combined with Lemma 2.4 and Theorem 2.5 it gives the direction from groupfree to circuits of the main theorem.
--
--   Differences from the source:
--   - reading: "simulates M" → the circuit outputs every state F^k_i for 1 ≤ i ≤ n and the accept bit; reason: the page does not define simulation; this is the stronger reading, which its proof builds within the same bound
--   - encoding: input symbols fed to a circuit, with no code named → an injective code α → {0,1}^b with b ≥ 1; reason: the page's circuits have boolean inputs; b = 0 is a one-letter alphabet with the empty code, for which a circuit has no nodes at all and nothing can be output
--   - encoding: "size O(n^3) and constant depth" → size ≤ C·n^3 and depth ≤ D for all n ≥ 1, with C, D depending on M and the code only; reason: this is what the O-notation says at n ≥ 1
--   - reading: "the state of flipflops F1,...,Fi−1" with no time index → every r_i, s_i reads the state vector from before the current letter (synchronous update); reason: the other reading makes Theorem 2.5 false, on the words whose second-to-last letter is 1
--   - encoding: a directed acyclic graph with input nodes labelled by variables → gates in topological order, one input node per variable; reason: merging input nodes with the same label only lowers the size; no instance changes
--   - encoding: an rs machine with flipflops F1,...,Fk → some machine with m flipflops, m = 0 allowed; reason: a machine with no flipflops behaves as a one-flipflop machine that never changes state, with the same accept bit, so no instance is added
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, Theorem 2.6, p.55; proof to p.56

import Definitions.Def_FanInSemigroup_Circuit
import Definitions.Def_FanInSemigroup_RSMachine

set_option autoImplicit false

namespace FanInSemigroup

/-- **Theorem 2.6.** Chandra, Fortune, Lipton, STOC 1983, p.55 (proof to p.56): "Suppose M is an rs
machine. Then there is a circuit of size O(n^3) and constant depth that simulates M".

**Formalization Note.** Letters are fed to the circuit through an injective code `α → {0,1}^b`.
"Simulates" is read in the strong sense the proof builds: on the code of a word `w` of length `n`
the circuit outputs every flipflop state `F^k_i`, `1 ≤ i ≤ n` (the output `Sum.inl (i, k)`, with
`i : Fin n` standing for time `i + 1`), and the accept bit (the output `Sum.inr ()`). `b ≥ 1`
excludes only a one-letter alphabet with the empty code, for which a circuit has no nodes. `D`, `C`
depend on the machine and the code, not on `n`. -/
theorem theorem_2_6 {α : Type*} {m : ℕ} (M : RSMachine α m) {b : ℕ} (hb : 1 ≤ b)
    (code : α → Fin b → Bool) (hcode : Function.Injective code) :
    ∃ D C : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∃ K : Circuit (Fin n × Fin b) ((Fin n × Fin m) ⊕ Unit),
        K.depth ≤ D ∧ K.size ≤ C * n ^ 3 ∧
        ∀ w : Fin n → α,
          let x : Fin n × Fin b → Bool := fun v => code (w v.1) v.2
          (∀ (i : Fin n) (k : Fin m),
            K.eval x (Sum.inl (i, k)) = M.run ((List.ofFn w).take (i.val + 1)) k) ∧
          (K.eval x (Sum.inr ()) = true ↔ List.ofFn w ∈ M.language) := by sorry

end FanInSemigroup
