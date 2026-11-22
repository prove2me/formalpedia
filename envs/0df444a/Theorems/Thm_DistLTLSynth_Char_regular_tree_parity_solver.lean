-- Prove2me | Theorems.Thm_DistLTLSynth_Char_regular_tree_parity_solver
-- name    : DistLTLSynth.Char.regular_tree_parity_solver
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T09:15:34.64325+00:00
-- url     : https://prove2.me/theorems/89897fbc-fe97-4061-bca6-bcbb0ecd3cc5
-- title:
--   Primitive-Recursive Solver and Regular Model Extraction for Parity Tree Specifications
-- statement:
--   Primitive-recursive decision procedure and regular model extraction for finite parity tree specifications (`TreeSpecCode`).
--
--   Let $\mathrm{ts}$ describe a $(b + 1)$-branching labeled tree language over $\mathrm{Fin}(A + 1)$ with root admissibility $\mathrm{tsRootOk}$, parent-direction-child compatibility $\mathrm{tsChildOk}$, and deterministic parity branch monitor $\mathcal{M} = \mathrm{tsDPA}(\mathrm{ts})$. There exist a primitive-recursive solver $\mathrm{solveTreePG}$, specification encoder $\mathrm{packTS}$, and primitive-recursive regular-tree label evaluator $\mathrm{unfoldLabelPacked}$ such that:
--
--   $$
--   \mathrm{solveTreePG}(\mathrm{ts}) \neq \mathrm{none} \iff \exists t : \{0, \dots, b\}^* \to \{0, \dots, A\},\; \mathrm{ValidAcceptingTree}(\mathrm{ts}, t),
--   $$
--
--   and whenever $\mathrm{solveTreePG}(\mathrm{ts}) = \mathrm{some}\,\sigma$, unfolding $\sigma$ along finite node addresses yields a valid accepting regular tree.
--
--   This theorem supplies the parity-game solver and regular-tree strategy synthesis required to decide symbolic component tree nonemptiness and construct realizing distributed algorithms in Theorem 3.4.
--
--   **Formalization Note** Factoring the specification encoder `packTS` from the two-argument evaluator `unfoldLabelPacked` keeps product-encoding arity minimal for `Primrec` composition.
-- source:
--   arXiv:2611.04561, Distributed LTL Synthesis under Arbitrary Message Adversaries, Section 3.3 (Lemma 3.13, p. 16)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine

namespace DistLTLSynth.Char

theorem regular_tree_parity_solver :
    ∃ (solveTreePG : TreeSpecCode → Option (List ℕ))
      (packTS : TreeSpecCode → ℕ)
      (unfoldLabelPacked : ℕ → List ℕ → ℕ),
      Primrec solveTreePG ∧
      Primrec packTS ∧
      Primrec₂ unfoldLabelPacked ∧
      (∀ (ts : TreeSpecCode) (σ : List ℕ),
        solveTreePG ts = some σ →
          ValidAcceptingTree ts (fun addr =>
            ⟨(unfoldLabelPacked (Nat.pair (packTS ts) (Encodable.encode σ)) (addr.map Fin.val)) % (ts.2.1 + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩)) ∧
      (∀ (ts : TreeSpecCode),
        solveTreePG ts ≠ none ↔
          ∃ t : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1), ValidAcceptingTree ts t) := by sorry

end DistLTLSynth.Char
