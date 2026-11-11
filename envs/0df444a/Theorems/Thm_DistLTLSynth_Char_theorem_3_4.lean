-- Prove2me | Theorems.Thm_DistLTLSynth_Char_theorem_3_4
-- name    : DistLTLSynth.Char.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:17:14.647654+00:00
-- url     : https://prove2.me/theorems/04547002-4426-477b-9049-a1c281fe4760
-- title:
--   Theorem 3.4 — given a DPA for A with nowhere-dense π(A) and ϕ, realizability is decidable and a realizing algorithm constructible
-- statement:
--   There are computable procedures $\mathrm{dec}$ and $\mathrm{con}$ that take a deterministic parity automaton (by its code) for a message adversary $A$ and an instance (alphabets and LTL formula $\varphi$) such that, whenever $\pi(A)$ is nowhere dense,
--   $$\mathrm{dec}(\mathcal A_{\mathrm{adv}},\varphi)=\mathrm{true}\iff \varphi\text{ is realizable under }A,$$
--   and if $\varphi$ is realizable under $A$ then $\mathrm{con}(\mathcal A_{\mathrm{adv}},\varphi)$ is a code computing the local output functions of an algorithm realizing $\varphi$ under $A$. This is the decidability direction of Theorem 1.2, uniform in the adversary.
--
--   Differences from the source:
--   - encoding: 'given a deterministic parity automaton for A … one can decide … and construct one' → Computable dec : DPACode × Instance → Bool and Computable con : DPACode × Instance → Nat.Partrec.Code, correct on every pair whose automaton's language has nowhere-dense image; reason: Mathlib's computability on finite codes; the construction returns a program for (f_1, f_2)
--   - encoding: an instance consists of finite nonempty alphabets X_1, X_2, Y_1, Y_2 (with the interpretation of atomic propositions) and an LTL formula → Instance = (k1, k2, m1, m2, token list) with X_p = Fin (k_p+1), Y_p = Fin (m_p+1); the formula is a prefix-notation token list over ℕ-indexed atoms; an atom whose index is out of range is false, and a token list that is not exactly one formula is a no-instance; reason: a standard primitive-recursive encoding (Primcodable from ℕ, List and products through a computable, definitional equivalence); every paper instance has a code, and the two extra cases are decidable syntactic checks, so they change no decidability question
--   - encoding: π(A) nowhere dense in [0, 1] → IsNowhereDense (piMap '' A) in ℝ; reason: π(A) ⊆ [0, 1] and [0, 1] is closed in ℝ, so nowhere density in the subspace and in ℝ coincide
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 12 (PDF 13), Theorem 3.4

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata

namespace DistLTLSynth.Char

/-- Theorem 3.4: given a deterministic parity automaton (by its code `c`) for a message
adversary `A` with nowhere-dense image `π(A)` and an instance (alphabets and LTL formula `ϕ`),
one can decide whether a distributed algorithm realizing `ϕ` under `A` exists, and construct
(a code computing) one if it does. -/
theorem theorem_3_4 :
    ∃ dec : DPACode × Instance → Bool, Computable dec ∧
      ∃ con : DPACode × Instance → Nat.Partrec.Code, Computable con ∧
        ∀ (c : DPACode) (I : Instance), IsNowhereDense (piMap '' c.lang) →
          (dec (c, I) = true ↔ I.Realizable c.lang) ∧
            (I.Realizable c.lang → I.RealizedByCode c.lang (con (c, I))) := by sorry

end DistLTLSynth.Char
