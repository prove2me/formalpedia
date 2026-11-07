-- Prove2me | Theorems.Thm_CosDensity_lemma_8_2
-- name    : CosDensity.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:11.993533+00:00
-- url     : https://prove2.me/theorems/f5350c5f-bc03-4c6d-a97b-b63375ef7f92
-- title:
--   Lemma 8.2 — a sparse nonnegative code with small $p$-th power correlations
-- statement:
--   Fix an integer $p>2$ and $\iota\in(0,1/2)$. There are constants $C,c_1,c_2>0$, depending only on $p$ and $\iota$, with the following property. Let $N=N(m)$ satisfy $N(m)/m^{p/2}\to 0$. Then there is a sequence $s(m)$ with $s(m)/\sqrt m\to0$ such that, for all sufficiently large $m$ with $m<N(m)$:
--
--   1. $c_1(N/m)^{1/(p-2)}\le s\le c_2(N/m)^{1/(p-2)}$;
--   2. there are $N$ distinct $s$-subsets $S_1,\dots,S_N$ of $[m]$ whose normalized incidence vectors $a_i=\mathbf 1_{S_i}/\sqrt s$ are distinct unit vectors with nonnegative coordinates satisfying, for every $i$,
--
--   $$\sum_{j\ne i}\langle a_i,a_j\rangle^p\le\iota\qquad\text{and}\qquad\sum_{j\ne i}\langle a_i,a_j\rangle\le C\Big(\frac Nm\Big)^{(p-1)/(p-2)} .$$
--
--   This sparse nonnegative code supplies the codewords of the hard instance: (35)–(36) are its two row bounds.
--
--   Differences from the source:
--   - reading: C = C(p, ι); m sufficiently large and m < N = o(m^{p/2}); s = Θ_{p,ι}((N/m)^{1/(p−2)}) and s = o(√m) → C, c₁, c₂ chosen from (p, ι) before a sequence N(m) with N(m)/m^{p/2} → 0; a sequence s(m) with s(m)/√m → 0; the conclusion eventually in m whenever m < N(m); reason: the asymptotic phrases quantify over the sequence N; the proof's constants depend on (p, ι) only
--   - encoding: N distinct unit vectors in ℝ^m_{≥0}, each a normalized incidence vector of an s-subset → an injective family of s-subsets S_i of Fin m with incUnit S_i injective, unit, nonnegative; reason: same objects
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.2, Lemma 8.2, pp.29–30 (pdf_page 30–31)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace
open Filter Topology

namespace CosDensity

/-- **Lemma 8.2** (a sparse nonnegative code). Q. Zhang, *Frequency Moments Beyond Equality:
Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.2,
Lemma 8.2, pp.29–30 (pdf_page 30–31).

Fix an integer `p > 2` and `ι ∈ (0, 1/2)`. There is `C = C(p, ι)` such that, for `m` sufficiently
large and `m < N = o(m^{p/2})`, there are `N` distinct unit vectors `a_1, …, a_N ∈ ℝ^m_{≥0}` with
`Σ_{j≠i} ⟨a_i, a_j⟩^p ≤ ι` and `Σ_{j≠i} ⟨a_i, a_j⟩ ≤ C (N/m)^{(p−1)/(p−2)}` for every `i`; each
`a_i` may be the normalized incidence vector of an `s`-subset of `[m]`, with
`s = Θ_{p,ι}((N/m)^{1/(p−2)})` and `s = o(√m)`.

**Formalization Note.** "`m` sufficiently large and `m < N = o(m^{p/2})`" is read for a sequence
`N : ℕ → ℕ` with `N(m)/m^{p/2} → 0`: the constants `C`, `c₁`, `c₂` (those of `Θ_{p,ι}`) are chosen
from `(p, ι)` before the sequence, and the conclusion holds for all large `m` with `m < N(m)`. The
subset size is a sequence `s(m)` with `s(m)/√m → 0`. The vectors are `a_i = 1_{S_i}/√s`
(`incUnit`); distinctness is injectivity. -/
theorem lemma_8_2 (p : ℕ) (hp : 2 < p) (ι : ℝ) (hι0 : 0 < ι) (hι1 : ι < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ N : ℕ → ℕ, Tendsto (fun m : ℕ => (N m : ℝ) / (m : ℝ) ^ ((p : ℝ) / 2)) atTop (𝓝 0) →
        ∃ s : ℕ → ℕ, Tendsto (fun m : ℕ => (s m : ℝ) / Real.sqrt m) atTop (𝓝 0) ∧
          ∀ᶠ m in atTop, m < N m →
            c₁ * ((N m : ℝ) / m) ^ (1 / ((p : ℝ) - 2)) ≤ s m ∧
            (s m : ℝ) ≤ c₂ * ((N m : ℝ) / m) ^ (1 / ((p : ℝ) - 2)) ∧
            ∃ S : Fin (N m) → Finset (Fin m), Function.Injective S ∧ (∀ i, (S i).card = s m) ∧
              Function.Injective (fun i => incUnit (S i)) ∧
              (∀ i, ‖incUnit (S i)‖ = 1 ∧ ∀ k, 0 ≤ incUnit (S i) k) ∧
              ∀ i, ∑ j ∈ Finset.univ.erase i, ⟪incUnit (S i), incUnit (S j)⟫ ^ p ≤ ι ∧
                ∑ j ∈ Finset.univ.erase i, ⟪incUnit (S i), incUnit (S j)⟫ ≤
                  C * ((N m : ℝ) / m) ^ (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by sorry

end CosDensity
