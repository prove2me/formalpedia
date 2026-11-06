-- Prove2me | Theorems.Thm_FastMinority_lemma_5_7
-- name    : FastMinority.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:05:25.780522+00:00
-- url     : https://prove2.me/theorems/4c3f006c-f8e7-4121-bb67-09f3a126eb8d
-- title:
--   Lemma 5.7 — on $M<x<R$: $n\,r(x/n)\le2n^{1-D}$ and $\Pr(X_{t+1}=0)\ge1-2n^{1-D}$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k$, let $D>2$, $M=\lfloor Dn\log n/k\rfloor$ and $R=\lfloor n/2-n\sqrt{(2D\log n)/k}\rfloor$. For every consensus-region state $x$, i.e. $M<x<R$, the expected number $\mathbb E[Y\mid X_t=x]=n\,r(x/n)$ of agents adopting the current majority satisfies
--   $$
--   n\,r(x/n)\le2n^{1-D}, \tag{5.6}
--   $$
--   and
--   $$
--   \Pr(X_{t+1}=0\mid X_t=x)\ge1-2n^{1-D}.
--   $$
--
--   Between $M$ and $R$ almost every agent switches to the current minority, so the next round is consensus with probability $1-O(n^{1-D})$. In particular these states are good for every constant $b>0$ once $n$ is large, so $\mathcal H$ is not empty.
--
--   **Formalization Note** $Y\sim\mathrm{Bin}(n,r(x/n))$, so its mean is written as $n\,r(x/n)$ with the printed formula for $r$; the update function $\mu$ of Section 5.2.1 is not formalized.
--
--   Differences from the source:
--   - reading: consensus-region state x → M < x < R; reason: the range the proof uses ('The lower boundary x > M', 'The upper boundary x < R'); at good states just above M′ the mean is about b, not 2n^{1−D}
--   - generalization: sufficiently large n, k = Θ(log² n) → every n, every odd k, every D > 2; reason: the proof's bounds e^{−kx/n} ≤ n^{−D} and Q(x/n) ≤ n^{−4D} hold for every n ≥ 1 and odd k ≥ 1; specializes
--   - encoding: E[Y | X_t = x] = µ(x) = n r(x/n) → n · rMaj k (x/n); reason: Y ∼ Bin(n, r(x/n)) has mean n r(x/n); µ is not formalized
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Lemma 5.7, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_FastMinority_rMaj
import Definitions.Def_FastMinority_midThr
import Definitions.Def_FastMinority_upThr

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Lemma 5.7** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.23 = PDF p.25): for every consensus-region state `x`,
`E[Y | X_t = x] = n r(x/n) ≤ 2 n^{1−D}` (5.6) and `Pr(X_{t+1} = 0 | X_t = x) ≥ 1 − 2 n^{1−D}`.

**Formalization Note** `Y ∼ Bin(n, r(x/n))` counts the agents adopting the current majority, so
`E[Y | X_t = x] = n r(x/n)` (`rMaj`). A consensus-region state is `M < x < R` (the range used by the
proof: "The lower boundary x > M", "The upper boundary x < R"). Stated for every `n`, every odd `k` and
every `D > 2`. -/
theorem lemma_5_7 (n k : ℕ) (hk : Odd k) (D : ℝ) (hD : 2 < D) (x : Fin (n + 1))
    (hM : midThr n k D < (x : ℕ)) (hR : (x : ℕ) < upThr n k D) :
    (n : ℝ) * rMaj k (((x : ℕ) : ℝ) / n) ≤ 2 * (n : ℝ) ^ (1 - D) ∧
      1 - 2 * (n : ℝ) ^ (1 - D) ≤ MinorityDynamics.actualKernel n k x 0 := by sorry

end FastMinority
