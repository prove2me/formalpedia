-- Prove2me | Theorems.Thm_CritWinSpin_p7b_forger_pointwise_impl
-- name    : CritWinSpin.p7b_forger_pointwise_impl
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:54:14.289036+00:00
-- url     : https://prove2.me/theorems/3ef7aaa9-97b3-4958-bbc0-1423833e9a37
-- title:
--   Uniform per-output PPT implementation of the two Theorem 7.2 forgers
-- statement:
--   Fix a binary Ising source, the lifted construction of Theorem 6.3, efficient schedules $k,T$, and a PPT learner $A$. There are PPT algorithms $B_{\mathrm{ext}}$ and $B_{\mathrm{amp}}$ with the following per-output property. For every sufficiently large security parameter, key, input sequence $F_{1:T}$, and binary configuration $y$, the probability that $B_{\mathrm{ext}}(P,F_{1:T})$ returns exactly $y$ and that $y\in\Omega$ has a message outside $\\{\\Psi(F_t)\\}$ is at least the extension score `extScore`; the analogous statement for $B_{\mathrm{amp}}$ uses `ampScore`.
--
--   Each score is formed by running the $T$ independent slot kernels, selecting the first $k$ accepted lifted configurations, invoking $A$ on the lifted instance, and scanning the output for the first configuration whose message was not seen in the training samples. It keeps only runs whose selected configuration is exactly $y$ and whose message is fresh against all $T$ inputs.
--
--   This pointwise formulation isolates the actual uniform-Machine construction in the proof of Theorem 7.2. Finite additivity over $y$ then gives the total fresh-forgery probabilities used on p.27.
--
--   **Formalization Note** The bound is required output by output rather than only after summing over outputs. This stronger, reusable interface avoids hiding any probability aggregation in the Turing-machine construction and permits exact domination by a PPT which simulates the same composite experiment.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §7, pp.26–27, construction of the PPT algorithm B in the proof of Theorem 7.2.

import Mathlib
import Definitions.Def_CritWinSpin_ForgerScore
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- There are uniform PPT machines whose per-output laws dominate the exact per-output scores of
the extension and amplification forgers. The score includes the T independent calls to the slot
machine, the first-k-accepted selection, the call to A on the lifted instance, and the fresh scan. -/
theorem p7b_forger_pointwise_impl (S : SpinLaw) (p : ℕ)
    (F : BilinearFamily) (src : BinarySource F) (C : ℝ) (hsrc : SourceProps F src C)
    (Ac Cc : ℕ) (liftF : Str → Str) (hliftF : CookPvsNP.PolyTimeComputable liftF)
    (slotM : PPT) (û : (d : ℕ) → (desc : Str) → WatersKey F desc d → ℚ) (d₁ : ℕ)
    (hlift : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      IsUhat S ((thetaQ p Ac Cc (src.n d) : ℚ) : ℝ) (cloudSize p Cc (src.n d)) (û d desc key) ∧
      liftF (encInst (src.ham d desc key)) =
        tupleCode [encInst (liftInst S p Ac Cc (src.ham d desc key) (û d desc key)),
          encRat (û d desc key)])
    (k T : ℕ → ℕ) (hk : EffPoly k) (hT : EffPoly T) (A : PPT) :
    ∃ (B_ext B_amp : PPT),
      (∀ d ≥ max 1 d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
        ∀ (Fs : Fin (T d) → BinCfg (src.n d)) (y : BinCfg (src.n d)),
        extScore S p Ac Cc slotM (src.ham d desc key) (û d desc key) (k := k d)
            (src.omega d desc key) (src.psi d desc key) Fs A y ≤
          B_ext.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
            (fun s => s = List.ofFn y ∧ GoodForge (src.omega d desc key) (src.psi d desc key) Fs y)) ∧
      (∀ d ≥ max 1 d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
        ∀ (Fs : Fin (T d) → BinCfg (src.n d)) (y : BinCfg (src.n d)),
        ampScore S p Ac Cc slotM (src.ham d desc key) (û d desc key) (k := k d)
            (src.omega d desc key) (src.psi d desc key) Fs A y ≤
          B_amp.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
            (fun s => s = List.ofFn y ∧ GoodForge (src.omega d desc key) (src.psi d desc key) Fs y)) := by sorry
