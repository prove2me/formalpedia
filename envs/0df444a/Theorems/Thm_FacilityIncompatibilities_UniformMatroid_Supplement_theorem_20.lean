-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_Supplement_theorem_20
-- name    : FacilityIncompatibilities.UniformMatroid.Supplement.theorem_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:15:40.958607+00:00
-- url     : https://prove2.me/theorems/44d80f5a-ac45-476e-a91d-773a07568c18
-- title:
--   Theorem 20 — no polynomial-time (1 − η) ln n-approximation with facility-specific client matroids unless P = NP
-- statement:
--   Fix $0<\eta<1$. Consider facility location with **facility-specific client matroids**: $n$ clients, $m$ facilities, and for every facility $i$ a matroid $\mathcal M_i$ with ground set $V_C$; an assignment $\sigma:V_C\to S$ is feasible if $\sigma^{-1}(i)$ is independent in $\mathcal M_i$ for every $i\in S$. Restrict to instances in which **all distances are $0$** and **all opening costs are equal** (to some rational $f\ge0$).
--
--   Suppose there are an oracle Turing machine $T$, a polynomial $p$ and a threshold $N$ such that, for every such instance with $n\ge N$ clients and every matroid family $(\mathcal M_i)$ for which $V_F$ is feasible, $T$ run on the input word (of length $B$) with the oracle of the family halts within $p(B)$ steps and outputs a facility set $S$ and a feasible assignment $\sigma:V_C\to S$ with
--
--   $$\sum_{i\in S}f_i+\sum_j d(j,\sigma(j))\ \le\ (1-\eta)\ln n\cdot\mathrm{OPT}.$$
--
--   Then $\mathbf P=\mathbf{NP}$.
--
--   This shows that the common client matroid of FL-MI cannot be replaced by facility-specific matroids: even with uniform opening costs and zero connection costs the problem is as hard to approximate as set cover, so in particular it has no constant-factor approximation unless $\mathbf P=\mathbf{NP}$.
--
--   **Formalization Note** The oracle answers a query consisting of the code of $i<m$ followed by an $n$-bit vector $w$ by whether $\{j:w_j=1\}$ is independent in $\mathcal M_i$, each answer costing one step. $\mathbf P$ and $\mathbf{NP}$ are those of the published `CookPvsNP_defs`. Nothing about the inapproximability of set cover is assumed. $\ln$ is the natural logarithm, $\mathrm{OPT}$ is in `ℝ≥0∞`.
--
--   Differences from the source:
--   - reading: a polynomial-time (1 − η) ln n-approximation, for every n → the ratio is required only on instances with at least N clients, N chosen together with the algorithm; reason: (1 − η) ln n < 1 for n < e^{1/(1−η)} (it is 0 at n = 1), where no algorithm meets it on instances with OPT > 0, so the literal all-n reading is vacuously true; the asymptotic reading is the meaningful one and implies the literal one (take N = 0)
--   - encoding: "admits no polynomial-time (1 − η) ln n-approximation unless P = NP" → (∃ oracle Turing machine T, polynomial p, threshold N with the ratio and step bound p(input length), outputting an encoded feasible solution) → P = NP, with Cook's P and NP; reason: the standard reading of "unless P = NP", with matroids accessed by oracle as throughout the paper (printed p.2)
--   - encoding: the matroids M_i → one oracle answering queries (code of i) ++ (n-bit vector), other queries answered false; V_F feasible as a hypothesis; reason: the paper's independence-oracle convention for a family of matroids; instances without any feasible solution have nothing to output (standing assumption, printed p.2)
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Theorem 20, Appendix B.2, printed p.24 / PDF p.25 (proof printed pp.24–25 / PDF pp.25–26)

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Supplement_Hardness

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid.Supplement

/-- **Theorem 20** (printed p.24 / PDF p.25): for every fixed `0 < η < 1`, facility location with
facility-specific client matroids admits no polynomial-time `(1 − η) ln n`-approximation unless
`P = NP`, even when all opening costs are uniform and all connection costs are zero, where `n` is
the number of clients.

Stated as: if some oracle Turing machine `T`, polynomial `p` and threshold `N` are such that, on
every encoded instance with at least `N` clients, all distances `0` and all opening costs equal
(and `≥ 0`), and every family of client matroids `(M_i)` (ground set the clients, `V_F`
feasible), the run of `T` with the family oracle halts within `p(B)` steps and outputs the code
of a feasible solution of cost at most `(1 − η) ln n · OPT`, then `P = NP`. -/
theorem theorem_20 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    (∃ (T : QAdvFew.PoQOracle.OTM) (p : Polynomial ℕ) (N : ℕ),
      ∀ (E : NUEncodedInstance) (Ms : Fin E.m → Matroid (Fin E.n)),
        N ≤ E.n → (∀ x y, E.d x y = 0) → (∀ i i', E.f i = E.f i') →
        (E.toFamilyInstance Ms).Valid → (∀ i, (Ms i).E = Set.univ) →
        (E.toFamilyInstance Ms).IsFeasible Finset.univ →
        ∃ t : ℕ, t ≤ p.eval E.encode.length ∧
          T.result (familyOracle Ms) E.encode t ≠ none ∧
          ∃ (S : Finset (Fin E.m)) (σ : Fin E.n → Fin E.m),
            T.output (familyOracle Ms) E.encode t = encodeSolution S σ ∧
            (E.toFamilyInstance Ms).IsFeasibleAssignment S σ ∧
            ENNReal.ofReal ((E.toFamilyInstance Ms).solCost S σ) ≤
              ENNReal.ofReal ((1 - η) * Real.log E.n) * (E.toFamilyInstance Ms).OPT) →
    PEqNP := by sorry

end FacilityIncompatibilities.UniformMatroid.Supplement
