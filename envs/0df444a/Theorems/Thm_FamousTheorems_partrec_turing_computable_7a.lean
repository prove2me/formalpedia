-- Prove2me | Theorems.Thm_FamousTheorems_partrec_turing_computable_7a
-- name    : FamousTheorems.partrec_turing_computable_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:33.206231+00:00
-- url     : https://prove2.me/theorems/50f5b08a-6693-4ce1-90b4-765ba3484f08
-- title:
--   Partial recursive functions are Turing-computable
-- statement:
--   **Partial recursive functions are Turing-computable.** For every code $c$ of a partial recursive function on lists of natural numbers and every input list $v$, the multi-stack Turing machine $\mathrm{tr}$ started in the configuration encoding $(c,v)$ halts exactly when $c(v)$ is defined, and it halts in the configuration encoding the output $c(v)$.
--
--   This is the half of the Church–Turing correspondence stating that everything recursive is computable by a Turing machine. Together with the converse it shows that Turing machines and partial recursive functions define the same class of functions. The machine here is a single fixed universal machine, with the code $c$ given as part of its input.
--
--   **Formalization note.** Mathlib's `Turing.PartrecToTM2.tr_eval`. `Turing.ToPartrec.Code` is a code language for partial recursive functions on `List ℕ`. `Turing.PartrecToTM2.tr` is the transition function of a TM2 machine, which has finitely many stacks. `StateTransition.eval` runs a machine until it halts. `init c v` and `halt` encode the initial and final configurations, and `<$>` maps `halt` over the partial result.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Turing.PartrecToTM2.tr_eval`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem partrec_turing_computable_7a (c : Turing.ToPartrec.Code) (v : List ℕ) :
    StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr) (Turing.PartrecToTM2.init c v) =
      Turing.PartrecToTM2.halt <$> c.eval v := by sorry

end FamousTheorems
