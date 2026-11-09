-- Prove2me | Theorems.Thm_DSICCompComp_appendix_B_opening
-- name    : DSICCompComp.appendix_B_opening
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:33:31.902121+00:00
-- url     : https://prove2.me/theorems/055883fd-09e1-450f-bb69-98fe4cff5adc
-- title:
--   Appendix B — $\inf\{c : \mathrm{SRev}_{n+c}(D^m) \ge \mathrm{Rev}^M_n(D^m)\} \ge \Omega(\sqrt{nm})$ for the §B.4 parameters
-- statement:
--   Let $D$ be the distribution of Section 3.2 and $M$ the mechanism of Section 3.3, with the parameters of §B.4: for a constant $\lambda$,
--   $$
--   \ell = \min\{m, \lfloor n/\lambda^3\rfloor\},\quad r = \lfloor n/2\rfloor,\quad b = \sqrt{\lambda/(n\ell)},\quad a = (\lambda n/\ell)^4,\quad t = \sqrt a,\quad \varepsilon = \frac{1}{nb},\quad T = 3 .
--   $$
--   Then
--   $$
--   \inf_{c\in\mathbb N\cup\{0\}}\bigl\{c : \mathrm{SRev}_{n+c}(D^m) \ge \mathrm{Rev}^M_n(D^m)\bigr\} \;\ge\; \Omega(\sqrt{nm}),
--   $$
--   that is: there are a constant $\lambda \ge 1$, a constant $C > 0$ and a threshold $N_0$ such that for all $n \ge N_0$, all $m$ with $2 \le m \le n$ and every integer $c \ge 0$ with $c < C\sqrt{nm}$,
--   $$
--   \mathrm{SRev}_{n+c}(D^m) < \mathrm{Rev}^M_n(D^m).
--   $$
--
--   Combined with $M \in \mathcal D$ (§3.3) and the regularity of $D$ (§3.2), this gives Theorem 3.1.
--
--   Differences from the source:
--   - reading: Ω(√nm), with λ "a (large) constant to be chosen later" → ∃ λ ≥ 1, ∃ C > 0, ∃ N₀ before ∀ n ≥ N₀ and ∀ m ∈ [2, n]; reason: the standard meaning of Ω with absolute constants; the range 2 ≤ m ≤ n of Theorem 3.1
--   - reading: inf{c : SRev_{n+c}(D^m) ≥ Rev^M_n(D^m)} ≥ C√(nm) → every c ∈ ℕ with c < C√(nm) has SRev_{n+c}(D^m) < Rev^M_n(D^m); reason: equivalent to the infimum bound; avoids sInf ∅ = 0 in ℕ
--   - reading: r = n/2 and ℓ = min{m, n/λ³} → r = ⌊n/2⌋ and ℓ = min{m, ⌊n/λ³⌋}; reason: the numbers of reserve bidders and of items are integers
--   - encoding: s = λ times a large constant → s does not appear; reason: s is internal to the proof (it only enters through the bound of §B.4)
--   - encoding: SRev_{n+c}(D^m) < Rev^M_n(D^m) → sRev in ℝ≥0∞, cast to EReal, < the published expRevenueN of M; reason: same comparison of extended reals
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix B, opening display, p.24 (pdf p.25), with the parameters of §B.4, p.33 (pdf p.34)

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model
import Definitions.Def_DSICCompComp_profileLaw
import Definitions.Def_DSICCompComp_sRev
import Definitions.Def_DSICCompComp_hardDist
import Definitions.Def_DSICCompComp_mechM

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Appendix B, opening display, with the parameters of §B.4 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Appendix B, p.24 (pdf p.25),
and §B.4, pp.33–34 (pdf pp.34–35)): for the distribution `D` of §3.2 and the mechanism `M` of
§3.3, `inf_{c ∈ ℕ ∪ {0}} {c : SRev_{n+c}(D^m) ≥ Rev^M_n(D^m)} ≥ Ω(√(nm))`, with
`r = n/2`, `b = √(λ/(nℓ))`, `a = (λn/ℓ)⁴`, `t = √a`, `ε = 1/(nb)`, `T = 3` and
`ℓ = min{m, n/λ³}` for a sufficiently large constant `λ`.

Lean reading: there are a constant `λ ≥ 1` (`lam`), a constant `C > 0` and a threshold `N₀` such
that for all `n ≥ N₀` and `2 ≤ m ≤ n`, with these parameters, every `c ∈ ℕ` with `c < C√(nm)`
has `SRev_{n+c}(D^m) < Rev^M_n(D^m)`.

**Formalization Note** `r = ⌊n/2⌋` and `ℓ = min{m, ⌊n/λ³⌋}` (the printed values are not integers
in general). The infimum bound is unfolded: `inf{c : SRev_{n+c} ≥ Rev^M_n} ≥ C√(nm)` iff every
`c < C√(nm)` has `SRev_{n+c} < Rev^M_n`. The proof-internal parameter `s` does not appear. -/
theorem appendix_B_opening :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → 2 ≤ m → m ≤ n →
      ∀ c : ℕ, (c : ℝ) < C * Real.sqrt ((n : ℝ) * m) →
        ((sRev (n + c) (fun _ : Fin m =>
            hardDist ((lam * n / (min m ⌊(n : ℝ) / lam ^ 3⌋₊ : ℕ)) ^ 4)
              (Real.sqrt (lam / (n * (min m ⌊(n : ℝ) / lam ^ 3⌋₊ : ℕ))))) : ℝ≥0∞) : EReal) <
          MultiItemRev.MultiBuyer.expRevenueN
            (profileLaw n fun _ : Fin m =>
              hardDist ((lam * n / (min m ⌊(n : ℝ) / lam ^ 3⌋₊ : ℕ)) ^ 4)
                (Real.sqrt (lam / (n * (min m ⌊(n : ℝ) / lam ^ 3⌋₊ : ℕ)))))
            (mechM n m (min m ⌊(n : ℝ) / lam ^ 3⌋₊) (n / 2)
              ((lam * n / (min m ⌊(n : ℝ) / lam ^ 3⌋₊ : ℕ)) ^ 4)
              (1 / (n * Real.sqrt (lam / (n * (min m ⌊(n : ℝ) / lam ^ 3⌋₊ : ℕ)))))
              (Real.sqrt ((lam * n / (min m ⌊(n : ℝ) / lam ^ 3⌋₊ : ℕ)) ^ 4)) 3) := by sorry

end DSICCompComp
