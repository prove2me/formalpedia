-- Prove2me | Theorems.Thm_FRouting_Supplement_theorem_1_5
-- name    : FRouting.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:23:49.254221+00:00
-- url     : https://prove2.me/theorems/2d44bc7f-7d3a-499b-9a98-1f6d35c758b5
-- title:
--   Theorem 1.5 — $(\mathcal T,t)$-uniform Clifford+T strategies give $f\in\mathbf{DTIME}((\mathcal T2^t)^c)$
-- statement:
--   There are universal constants $c\ge1$ and $\varepsilon_0>0$ with the following property. Let $\mathcal T:\mathbb N\to\mathbb N$ be nondecreasing and time-constructible with $\mathcal T(n)\ge n$, let $t:\mathbb N\to\mathbb N$ be arbitrary, and let $f=(f_n)$ with $f_n:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}$. If some $(\mathcal T,t)$-uniform Clifford+T $f$-routing strategy on qubits is $(1-\varepsilon)$-correct on every input $(x,y)$ at every input length $n$, for one $\varepsilon$ with $0\le\varepsilon\le\varepsilon_0$, then the language $L_f=\{x\circ y: f_n(x,y)=1\}$ satisfies
--   $$L_f\in\mathbf{DTIME}\bigl((\mathcal T\,2^{t})^{c}\bigr),$$
--   the bound at input length $m=2n$ being $(\mathcal T(n)\,2^{t(n)})^c$.
--
--   Correctness is measured by the root fidelity of the verifier's tested qubits with the EPR pair. Compared with the general goal (Theorem 5.2, $f\in\mathbf{QSZK}$), the Clifford+T restriction gives a deterministic bound that is exponential only in the number of magic gates.
--
--   Differences from the source:
--   - reading: a (𝒯, t)-uniform Clifford+T strategy (stated in the overview) → qubit strategies, d = 2; reason: p.5: "we focus on d = 2 in this overview"; the general-d form is Corollary 6.4, which is not a theorem of the paper
--   - reading: Clifford+T circuits and magic gates (no gate list) → gates {H, S, CNOT, T}, magic count = number of T gates; reason: the standard Clifford+T set; T† = S³T costs one magic gate as usual
--   - generalization: five fixed uniform generator machines, including unrestricted-time post-communication generators → the resource and pre-communication generators are machines while the post-communication channels are arbitrary; reason: the proof never runs the post generators, and every source strategy specializes by forgetting them
--   - encoding: DTIME and circuit-running time (standard models left implicit) → the published binary-string machine model with exact output bits, explicit circuit size and width bounds, and budget max(1, 𝒯(n)); reason: fixed standard models and the length-zero convention, changing no positive-time instance
--   - encoding: f ∈ DTIME((𝒯2^t)^c), 𝒯 and t functions of n = |x| → L_f ∈ DTIME(m ↦ (𝒯(⌊m/2⌋)·2^{t(⌊m/2⌋)})^c) on input length m; reason: |x ∘ y| = 2n; the base mission's convention (theorem_5_2), with the time budget max(1, ·)
--   - encoding: c ≥ 1 a real constant → c a natural number ≥ 1; reason: the base 𝒯·2^t is 0 or ≥ 1, so a real exponent can be replaced by its ceiling
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 1.5, p.5 (Definition 6.1, p.23)

import Definitions.Def_FRouting_Supplement_UniformCTStrategy
import Definitions.Def_FRouting_Supplement_InDTIME

set_option autoImplicit false

namespace FRouting.Supplement

/-- **Theorem 1.5 — security against `(𝒯, t)`-uniform Clifford+T strategies.** Renard, *Computational
Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 1.5, p.5: "There exist
universal constants ε₀ > 0 and c ≥ 1 such that if a (𝒯, t)-uniform Clifford+T f-routing strategy is
(1 − ε)-correct on every input at every input length for some 0 ≤ ε ≤ ε₀, then f ∈ DTIME((𝒯2ᵗ)ᶜ)."

**Formalization Note** Qubit strategies (`d = 2`): p.5 says "we focus on d = 2 in this overview".
`c` and `ε₀` come before `𝒯, t, f` and the strategy; `ε` is one number for all `n`. `𝒯` is as in
Definition 1.2 (time-constructible, nondecreasing, `𝒯(n) ≥ n`), exactly as in the published goal
`FRouting.theorem_5_2`; `t` has no hypothesis. `f ∈ DTIME(B)` means `L_f ∈ DTIME(B)`, and on input length
`m` of `L_f` the bound is taken at `n = m/2` (`|x ∘ y| = 2n`), the base mission's convention. -/
theorem theorem_1_5 :
    ∃ (c : ℕ) (ε₀ : ℝ), 1 ≤ c ∧ 0 < ε₀ ∧
      ∀ (T t : ℕ → ℕ), IsTimeConstructible T → Monotone T → (∀ n, n ≤ T n) →
        ∀ (f : ∀ n, (Fin n → Bool) → (Fin n → Bool) → Bool) (S : UniformCTStrategy T t) (ε : ℝ),
          0 ≤ ε → ε ≤ ε₀ → (∀ n x y, (S.toRouting n).IsCorrectOn (f n) ε x y) →
          InDTIME (languageOf f) (fun m => (T (m / 2) * 2 ^ t (m / 2)) ^ c) := by sorry

end FRouting.Supplement
