-- Prove2me | Theorems.Thm_CertRandQROM_lemma_7_7_events
-- name    : CertRandQROM.lemma_7_7_events
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:58.290449+00:00
-- url     : https://prove2.me/theorems/ceb8631e-38ae-43cb-aedf-f850371ad34e
-- title:
--   Lemma 7.7 — Event1 and Event2 give an $x_h$ with Event3
-- statement:
--   Let $h$ be an oracle that satisfies Event1 (acceptance probability $\ge\delta$ and $H_\infty(\mathcal A^h_\top)\le h_\infty$, with $\delta>0$) and Event2 (with $\alpha=\delta\cdot2^{-h_\infty}$ and $s$). Then there is an $x_h$ such that $(h,x_h)$ satisfies Event3 (with the same $\alpha$ and $s$):
--
--   $$
--   \mathrm{Event1}(h)\ \wedge\ \mathrm{Event2}(h)\ \Longrightarrow\ \exists x_h:\ \mathrm{Event3}(h,x_h).
--   $$
--
--   Combined with Lemma 7.3 this bounds $\Pr_H[\mathrm{Event1}\wedge\mathrm{Event2}]$ by $2(1-p)^s/\alpha$.
--
--   Differences from the source:
--   - generalization: the code C_λ, s = ⌈n/10⌉, δ(λ) = λ^{−t}, h∞(λ) = ⌈λ^c/3⌉ of §7.3 → any code C ⊆ Σ^n, any s, h∞ ∈ ℕ and δ > 0; reason: the proof uses none of these choices; §7.3's values are an instance
--   - encoding: δ(λ) = λ^{−t} → hypothesis 0 < δ; reason: λ^{−t} > 0 for λ ≥ 1; it excludes the case δ ≤ 0 with no correct string, where the conditional law is 0/0
--   - generalization: A parametrized by Q ≥ 1 (§3.2) → any Q : ℕ, including Q = 0; reason: for Q ≥ 1 it is the paper's statement; Q = 0 is an extra trivial case
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 7.7, p.44 (PDF p.46); Events 1–3, §7.3, pp.43–44

import Mathlib
import Definitions.Def_CertRandQROM_Event1
import Definitions.Def_CertRandQROM_Event2
import Definitions.Def_CertRandQROM_Event3

namespace CertRandQROM

/-- **Lemma 7.7** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…), p.44): let `h` be any
oracle satisfying Event1 (with `δ > 0` and `h∞`) and Event2 (with `α = δ · 2^{−h∞}` and `s`).
Then there is an `x_h` such that `(h, x_h)` satisfies Event3 (with the same `α` and `s`).

**Formalization Note** `δ > 0` is the standing `δ(λ) = λ^{−t}` of §7.3. The statement holds for
every code `C`, every algorithm with outputs `Option (Σ^n)` and every `s` (the paper's is
`⌈n/10⌉`). -/
theorem lemma_7_7_events {n : ℕ} {S W : Type} [Fintype S] [DecidableEq S] [Fintype W]
    [DecidableEq W] {Q : ℕ} (C : Finset (Fin n → S))
    (A : QueryAlg (Fin n × S) W (Option (Fin n → S)) Q) (h : Fin n × S → Bool) (δ : ℝ)
    (hδ : 0 < δ) (hInf s : ℕ) (h₁ : Event1 C A δ hInf h)
    (h₂ : Event2 C A (δ * ((2 : ℝ) ^ hInf)⁻¹) s h) :
    ∃ x : Fin n → S, Event3 C A (δ * ((2 : ℝ) ^ hInf)⁻¹) s h x := by sorry

end CertRandQROM
