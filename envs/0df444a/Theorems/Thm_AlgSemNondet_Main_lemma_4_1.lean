-- Prove2me | Theorems.Thm_AlgSemNondet_Main_lemma_4_1
-- name    : AlgSemNondet.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:46:58.1802+00:00
-- url     : https://prove2.me/theorems/4bf0e79b-04a4-46ff-bd6f-cf0053e27082
-- title:
--   Lemma 4.1 — syntactic invariance: $M_\pi$ on $\pi(w)$ runs through $\pi(C_0), \pi(C_1), \dots$
-- statement:
--   Let $M$ be a classical Turing machine with input alphabet $\Sigma \subseteq \Gamma$ and blank $B \in \Gamma \setminus \Sigma$, and let $\pi$ be a bijection of $\Gamma$ with $\pi(B) = B$ and $\pi(\Sigma) = \Sigma$. If $M$ on input $w$ goes through the configuration sequence $C_0, C_1, C_2, \dots$, then $M_\pi$ on input $\pi(w)$ goes through $\pi(C_0), \pi(C_1), \pi(C_2), \dots$: for every $n$,
--   $$\operatorname{run}(M_\pi, \pi(w), n) = \pi\big(\operatorname{run}(M, w, n)\big),$$
--   including that $M_\pi$ stops at exactly the step where $M$ stops.
--
--   Differences from the source:
--   - encoding: the configuration sequence C₀, C₁, … (finite when the machine stops) → run : ℕ → Option Config, none from the first step after the machine stops, and the equality for every n; reason: the same sequence with its length
--   - reading: Definition 3.1 gives only a partial δ → the computation stops when δ is undefined or the state is q_accept or q_reject; reason: the standard convention for a machine that "accepts or rejects" (p.7); M_π has the same distinguished states, so the lemma does not depend on the choice
--   - encoding: a tape with the input written on it, head on the leftmost non-blank symbol → tape ℤ → Γ with the input in cells 0, …, n − 1, head at the index of the first non-blank letter (0 when there is none); reason: the source fixes no coordinates
--   - generalization: input w = w₁⋯wₙ, an input string over Σ → any word w over Γ; reason: the statement for w ∈ Σ* is the special case; the paper applies machines to inputs over Γ∖{B} (Theorem 4.5)
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Lemma 4.1, pp.14-15, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib
import Definitions.Def_AlgSemNondet_Main_TuringMachine
import Definitions.Def_AlgSemNondet_Main_relabel

namespace AlgSemNondet.Main

/-- Lemma 4.1 (syntactic invariance): for a bijection `π` of `Γ` with `π(B) = B` and
`π(Σ) = Σ`, the run of `M_π` on `π(w)` is, step for step, the `π`-image of the run of `M` on
`w` (including where it stops). -/
theorem lemma_4_1 {Q Γ : Type*} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    {B : Γ} (M : TuringMachine Q Γ B) (π : Equiv.Perm Γ) (hπB : π B = B)
    (hπInput : π '' M.inputAlphabet = M.inputAlphabet) (w : List Γ) (n : ℕ) :
    (M.relabel π).run (w.map π) n = (M.run w n).map (Config.relabel π) := by sorry

end AlgSemNondet.Main
