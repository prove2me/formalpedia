-- Prove2me | Theorems.Thm_DetParamSVP_theorem_3_4_correct
-- name    : DetParamSVP.theorem_3_4_correct
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:30.470348+00:00
-- url     : https://prove2.me/theorems/bb1e6e5b-b61f-49a1-955c-f424c2a3aaaf
-- title:
--   Proof of Theorem 3.4 — $(q,(z^j),-\sum_\ell e_{y_\ell},(x_1,\dots,x_m))$ is a locally dense lattice for every prime $q>T$
-- statement:
--   Fix $p\ge1$ and positive integers $m,d,D,h,k$ with $D\ge2$, $k\ge2$, $d^p\le h$ and $D^p<2k$; put $L=k-1$, $W=k-1+2h$, and let $T$ be the bound of Eq. (7). Let $q>T$ be prime and let $y_1,\dots,y_L,x_1,\dots,x_m\in\mathbb F_q$ be distinct. Then the tuple $(q,H,s,S)$ with
--
--   $$H=(z^j)_{0\le j<k,\ z\in\mathbb F_q},\qquad s=-\sum_{\ell=1}^{L}e_{y_\ell},\qquad S=(x_1,\dots,x_m)$$
--
--   is a locally dense lattice with parameters $(p,m,d,D,W)$.
--
--   This is the mathematical content of Theorem 3.4, separated from the running-time analysis.
--
--   Differences from the source:
--   - generalization: a prime q with T < q < 2T (chosen by Lemma 2.12) → any prime q > T; reason: the upper bound 2T matters only for the running time; the source q satisfies the hypothesis
--   - encoding: coordinates indexed by F_q; distinct y, x → coordinates ZMod q; injectivity of Sum.elim y x; reason: same objects
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.4, pp.19–23 (conclusion p.23)

import Definitions.Def_DetParamSVP_LocallyDense
import Definitions.Def_DetParamSVP_RSConstruction

set_option autoImplicit false

namespace DetParamSVP

/-- **Proof of Theorem 3.4: correctness of the construction.** Under the hypotheses of Theorem 3.4
(positive integers `m, d, D, h, k` with `D ≥ 2`, `k ≥ 2`, `d^p ≤ h`, `D^p < 2k`), for every prime
`q > T` (`T` of Eq. (7)) and distinct `y₁, …, y_L, x₁, …, x_m ∈ F_q` (`L = k − 1`), the tuple
`(q, H, s, S)` with `H = (z^j)_{0≤j<k, z∈F_q}`, `s = −∑_ℓ e_{y_ℓ}` and `S = (x₁, …, x_m)` is a
locally dense lattice with parameters `(p, m, d, D, W)`, `W = k − 1 + 2h`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.4, pp.19–23 (conclusion on p.23).

**Formalization Note.** The coordinates are the elements of `ZMod q`. The paper also has
`q < 2T`, which matters only for the running time; here `q` is any prime above `T`. `W` is
computed in `ℕ` with `k ≥ 2`. -/
theorem theorem_3_4_correct (p : ℝ) (hp : 1 ≤ p) (m d D h k : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hD0 : 0 < D) (hh : 0 < h) (hk0 : 0 < k) (hD : 2 ≤ D) (hk : 2 ≤ k) (hdh : (d : ℝ) ^ p ≤ h)
    (hDk : (D : ℝ) ^ p < 2 * k) (q : ℕ) [Fact q.Prime] (hT : Tbound m D h k < q)
    (y : Fin (k - 1) → ZMod q) (x : Fin m → ZMod q) (hyx : Function.Injective (Sum.elim y x)) :
    IsLocallyDenseLattice p m d D (k - 1 + 2 * h) q (vandermondeH q k) (rsCenter y) x := by sorry

end DetParamSVP
