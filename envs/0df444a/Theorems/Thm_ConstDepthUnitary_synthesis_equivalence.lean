-- Prove2me | Theorems.Thm_ConstDepthUnitary_synthesis_equivalence
-- name    : ConstDepthUnitary.synthesis_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:50:11.431295+00:00
-- url     : https://prove2.me/theorems/0149aace-7408-4aff-be31-f8715f9bbb7b
-- title:
--   Lemma 3.1 — the equivalent formulations of unitary synthesis
-- statement:
--   Let $\mathcal U_q\supseteq\mathcal O_q\supseteq\mathcal S_q\supseteq\mathcal T_q$ be the classes of $q$-qubit unitaries, real unitaries, real symmetric involutions and traceless real symmetric involutions. There is a universal constant $a$ such that, for every $q,s,d,w,\varepsilon$ (size, depth, width, error):
--   $$\mathrm{Synth}(\mathcal U_q;s,d,w,\varepsilon)\Rightarrow\mathrm{Synth}(\mathcal S_q;s,d,w,\varepsilon)\Rightarrow\mathrm{Synth}(\mathcal T_q;s,d,w,\varepsilon),$$
--   $$\mathrm{Synth}(\mathcal T_{q+1};s,d,w,\varepsilon)\Rightarrow\mathrm{Synth}(\mathcal O_q;s+a,d+a,w+a,\varepsilon),$$
--   $$\mathrm{Synth}(\mathcal O_{q+1};s,d,w,\varepsilon)\Rightarrow\mathrm{Synth}(\mathcal U_q;s+a,d+a,w+a,\varepsilon).$$
--   The same four implications hold in the oracle model, for one fixed query algorithm, any oracle class and an unchanged number of queries. Each holds both with fan-out gates allowed and for one- and two-qubit gates only.
--
--   So synthesis for all unitaries reduces to synthesis for traceless real symmetric involutions, at a factor of at most four in the dimension and an additive constant in the resources.
--
--   Differences from the source:
--   - encoding: items 1–4 with Θ(s), Θ(d), Θ(w), N′ = Θ(N) → the printed "In fact" sentence with an explicit additive constant and q + 1 qubits for each doubling; reason: it implies the Θ form; a qubit register has dimension 2^q
--   - reading: oracle model, class of oracles unspecified → an arbitrary oracle class Ω and any oracle size t, with exact query count; reason: footnote 9 only says the oracle depends on U
--   - encoding: "(and number of oracle queries q)" and a circuit model left open → both the plain and the oracle model, each with and without fan-out; reason: the printed lemma covers both models and the reductions add only one-qubit gates
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.1, pp.14–15

import Mathlib
import Definitions.Def_ConstDepthUnitary_Synth

namespace ConstDepthUnitary

/-- Lemma 3.1 (equivalent formulations of unitary synthesis): the reductions
`(1) ⇒ (3) ⇒ (4) ⇒ (2) ⇒ (1)` between all unitaries, real symmetric involutions, traceless ones and real
unitaries, with at most a factor two in the dimension per step, a universal additive constant `a` in size,
depth and width, and an unchanged number of oracle queries. Stated for plain circuits and for oracle circuits
(a fixed query algorithm, footnote 9), each with fan-out allowed (`std = false`) and without (`std = true`).

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.1, pp.14–15.

**Formalization Note** The `Θ(·)` form of items 1–4 follows from the printed "In fact" sentence, which is
what is stated. Passing from `q` to `q + 1` qubits doubles the dimension. The oracle class `Ω` is arbitrary. -/
theorem synthesis_equivalence :
    ∃ a : ℕ,
      (∀ (std : Bool) (q s d w : ℕ) (ε : ℝ),
        (Synth std (unitaryClass q) s d w ε → Synth std (symInvolutionClass q) s d w ε) ∧
        (Synth std (symInvolutionClass q) s d w ε → Synth std (tracelessClass q) s d w ε) ∧
        (Synth std (tracelessClass (q + 1)) s d w ε →
          Synth std (orthogonalClass q) (s + a) (d + a) (w + a) ε) ∧
        (Synth std (orthogonalClass (q + 1)) s d w ε →
          Synth std (unitaryClass q) (s + a) (d + a) (w + a) ε)) ∧
      (∀ (std : Bool) (t : ℕ) (Ω : Set (Matrix (Fin t → Bool) (Fin t → Bool) ℂ))
          (q qq s d w : ℕ) (ε : ℝ),
        (SynthOracle std (unitaryClass q) Ω qq s d w ε →
          SynthOracle std (symInvolutionClass q) Ω qq s d w ε) ∧
        (SynthOracle std (symInvolutionClass q) Ω qq s d w ε →
          SynthOracle std (tracelessClass q) Ω qq s d w ε) ∧
        (SynthOracle std (tracelessClass (q + 1)) Ω qq s d w ε →
          SynthOracle std (orthogonalClass q) Ω qq (s + a) (d + a) (w + a) ε) ∧
        (SynthOracle std (orthogonalClass (q + 1)) Ω qq s d w ε →
          SynthOracle std (unitaryClass q) Ω qq (s + a) (d + a) (w + a) ε)) := by sorry

end ConstDepthUnitary
