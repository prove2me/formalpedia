-- Prove2me | Theorems.Thm_CosDensity_lemma_8_7
-- name    : CosDensity.lemma_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:16.233215+00:00
-- url     : https://prove2.me/theorems/45a05cdc-5739-4395-87b6-49bbc9205d19
-- title:
--   Lemma 8.7 — $\sum_{i\ne q}Z_i^p\le\nu Q^p$
-- statement:
--   Fix an integer $p>2$ and $\nu>0$. There is a code parameter $\iota\in(0,1/2)$ such that, for every constant $C_R>0$, there is $\bar c>0$ such that for every $c_N\in(0,\bar c]$ there is $m_0$ with the following property. For $m\ge m_0$ and $N=m\lfloor c_Nm^{\rho_p-1}\rfloor$, let $a_1,\dots,a_N$ be unit codewords with nonnegative coordinates satisfying
--
--   $$R_i=1+\sum_{r\ne i}\langle a_i,a_r\rangle\le C_RR_{\max}\quad(35)\qquad\text{and}\qquad\sum_{i\ne q}\langle a_i,a_q\rangle^p\le\iota\ \text{ for every }q\quad(36),$$
--
--   and let $\chi$ be a balanced coloring. Then for every $z$ and every query $q$, with $Z_i$ the code responses of $P(z,q)$,
--
--   $$\sum_{i\ne q}Z_i^p\le\nu\,Q^p .$$
--
--   The nonqueried responses are noise; this lemma makes them a small fraction of the queried signal.
--
--   Differences from the source:
--   - reading: ι and then the constant c_N can be chosen; the code is that of Lemma 8.2 with (35)–(36) → ∃ ι, then ∀ C_R ∃ c̄ ∀ c_N ∈ (0, c̄] ∃ m₀ ∀ m ≥ m₀; every unit nonnegative code satisfying (35) with C_R and (36) with ι, every balanced coloring, every z; reason: the paper's C_R = C(p, ι) + 1 is fixed between ι and c_N; quantifying it universally covers it, and (35)–(36) are the only code properties the proof uses
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.6, Lemma 8.7, p.34 (pdf_page 35), with (35)–(36), p.33 (pdf_page 34)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **Lemma 8.7** (nonqueried responses are small). Q. Zhang, *Frequency Moments Beyond Equality:
Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.6,
Lemma 8.7, p.34 (pdf_page 35), with (35)–(36), p.33 (pdf_page 34).

For every `ν > 0`, the code parameter `ι` and then the constant `c_N` can be chosen so that, for
every query `q`, `Σ_{i≠q} Z_i^p ≤ ν Q^p`.

**Formalization Note.** Order of choices: `ι` from `(p, ν)`; then for every constant `C_R` of
(35), a bound `c̄`; then for every `c_N ∈ (0, c̄]` a threshold `m₀`. For `m ≥ m₀`,
`N = m ⌊c_N m^{ρ_p−1}⌋`, every code `a` of unit nonnegative vectors satisfying (35)
`R_i ≤ C_R R_max` and (36) `Σ_{i≠q} ⟨a_i, a_q⟩^p ≤ ι`, every balanced coloring, every `z` and
every `q`, the bound holds with `Z_i` the code response of the sum of `P(z, q)`. -/
theorem lemma_8_7 (p : ℕ) (hp : 2 < p) (ν : ℝ) (hν : 0 < ν) :
    ∃ ι : ℝ, 0 < ι ∧ ι < 1 / 2 ∧ ∀ CR : ℝ, 0 < CR → ∃ cbar : ℝ, 0 < cbar ∧
      ∀ cN : ℝ, 0 < cN → cN ≤ cbar → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        ∀ (a : Fin (codeLength p cN m) → EuclideanSpace ℝ (Fin m))
          (χ : Fin (codeLength p cN m) → Fin m),
          IsUnitNonnegCode a → IsBalanced χ →
          (∀ i, rowSum a i ≤ CR * rMax p (codeLength p cN m) m) →
          (∀ q, ∑ i ∈ Finset.univ.erase q, ⟪a i, a q⟫ ^ p ≤ ι) →
          ∀ (z : Fin (codeLength p cN m) → Bool) (q : Fin (codeLength p cN m)),
            ∑ i ∈ Finset.univ.erase q, codeResp a i (hardStream p a χ z q).sum ^ p ≤
              ν * queryAmp p m ^ p := by sorry

end CosDensity
