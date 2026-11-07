-- Prove2me | Theorems.Thm_DDNNFNeg_fact_3_3
-- name    : DDNNFNeg.fact_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:44.824135+00:00
-- url     : https://prove2.me/theorems/12c151ce-17f6-4453-bc40-8167ebd88acc
-- title:
--   Fact 3.3, first sentence (corrected: the DNNF may use constant leaves) — nFBDD → DNNF and uFBDD → d-DNNF with constant-factor size
-- statement:
--   **Fact 3.3** (first sentence). There is an absolute constant $C$ such that:
--
--   1. for every nFBDD $B$ over a finite variable set $X$ there is an equivalent DNNF of size at most $C \cdot |B|$;
--   2. for every uFBDD $B$ over $X$ there is an equivalent d-DNNF of size at most $C \cdot |B|$.
--
--   Here "equivalent" means computing the same function $\{0,1\}^X \to \{0,1\}$, and $|B|$ is the number of vertices of $B$.
--
--   This is the translation that turns the linear-size OBDDs of Proposition 5.1 into linear-size d-DNNFs.
--
--   **Formalization Note** As printed, with the literal-only input gates of §3.1, the statement is false: the FBDD over $\{x_1\}$ whose starting vertex tests $x_1$ with both edges into the $0$-sink (plus an unreached $1$-sink) is read-once, deterministic and unambiguous and computes the constant $0$, while every constant-free DNNF is satisfiable. The output circuit is therefore allowed constant leaves, as §4 (p.10) also allows "when simplifying circuits".
--
--   Differences from the source:
--   - correction: equivalent DNNF (resp. d-DNNF) with literal input gates only → the output DNNF (resp. d-DNNF) may also use constant leaves; reason: the printed statement is false: the FBDD on {x₁} testing x₁ with both edges into the 0-sink computes 0, and no constant-free DNNF computes 0 (every constant-free DNNF is satisfiable)
--   - generalization: nFBDD with sinks labelled 1 and 0 → branching program that may have several sinks with the same label; reason: a program with one sink of each label is a special case; the input class is larger
--   - encoding: the constant factor → one natural-number constant C, chosen before the variable set and the program; reason: the paper's constant is absolute
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Fact 3.3 (first sentence), p.9

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_Computes
import Definitions.Def_DDNNFNeg_NNF_IsDDNNF
import Definitions.Def_DDNNFNeg_BDD_Computes
import Definitions.Def_DDNNFNeg_BDD_IsReadOnce
import Definitions.Def_DDNNFNeg_BDD_IsUnambiguous

namespace DDNNFNeg

/-- **Fact 3.3**, first sentence (corrected: the DNNF may use constant leaves)
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.9): for every nFBDD (respectively uFBDD) there is an equivalent DNNF (respectively
d-DNNF) of size at most a constant factor greater. The constant `C` is absolute: it does not
depend on the variable set or on the branching program.

**Formalization Note** An nFBDD is a `BDD` with `IsReadOnce`, a uFBDD one that is moreover
`IsUnambiguous`; "equivalent" means computing the same function on `{0,1}^X`. As printed, with
the literal-only input gates of §3.1, the statement is false: the FBDD on `X = {x₁}` whose
starting vertex tests `x₁` with both edges into the `0`-sink (plus an unreached `1`-sink)
computes the constant `0`, and no constant-free DNNF is unsatisfiable. The output circuit is
therefore allowed constant leaves (`IsDNNF` without `IsConstFree`). Several sinks with the same
label are allowed in the input (a generalization). -/
theorem fact_3_3 :
    (∃ C : ℕ, ∀ (X : Type*) [Fintype X] [DecidableEq X] (B : BDD X), B.IsReadOnce →
      ∀ f : (X → Bool) → Bool, B.Computes f →
        ∃ D : NNF X, D.IsDNNF ∧ D.Computes f ∧ D.size ≤ C * B.size) ∧
    (∃ C : ℕ, ∀ (X : Type*) [Fintype X] [DecidableEq X] (B : BDD X), B.IsReadOnce →
      B.IsUnambiguous → ∀ f : (X → Bool) → Bool, B.Computes f →
        ∃ D : NNF X, D.IsDDNNF ∧ D.Computes f ∧ D.size ≤ C * B.size) := by sorry

end DDNNFNeg
