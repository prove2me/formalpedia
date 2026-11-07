-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_2_4
-- name    : AvgValueAlloc.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:43.806193+00:00
-- url     : https://prove2.me/theorems/cdddcca0-b81d-4d3f-a022-98064d09cca4
-- title:
--   Lemma 2.4 — Benchmark capture, with (7) and the local capture
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$ and $H_G(M,Z)=\max_X\{W(X)+G_Z(B(X))\}$.
--
--   1. For a live multiset $Q$ of $T$ items with $r=\lfloor T/3\rfloor\ge1$, in uniform order, with $r$ funding positions $M$ followed by $r$ service positions $Z$:
--   $$
--   \mathbb E\,H_G(M,Z)\ \ge\ \frac{r^2\,\mathrm{OPT}_{\mathrm{off}}(Q)}{4T(T-1)}\ \ge\ \frac{\mathrm{OPT}_{\mathrm{off}}(Q)}{100}.
--   $$
--   2. For every finite law $D$ and $r$ with $2r\le T$, $r\ge T/5$, with $g(B)=\mathbb E_{Z\sim D^r}G_Z(B)$:
--   $$
--   \mathbb E_{M\sim D^r}\max_X\{W(X)+g(B(X))\}\ \ge\ \mathrm{OPT}_{\mathrm{on}}(D,T)/2280.\tag{7}
--   $$
--   3. If every sponsor of $Q$ is local and $r=\lfloor T/3\rfloor\ge1$, then with $K\sim\mathrm{Bin}(2r,1/2)$, a fair shift $s$, a uniform order, funding $M$ the $r$ positions after the first $K$, and service $Z$ the next $2r-K$ positions:
--   $$
--   \mathrm{OPT}_{\mathrm{off}}(Q)\le 200\,\mathbb E\,H^s_L(M,Z).
--   $$
--
--   These capture statements compare the learner's funding objectives with the offline and causal benchmarks.
--
--   Differences from the source:
--   - generalization: Lemma 2.4 as printed → also clause 3, the local capture OPT_off(Q) ≤ 200 E H^s_L(M, Z) stated in its proof (p.7); reason: the all-local row of Table 1 uses it (§4, p.10); the printed clauses are unchanged
--   - encoding: r funding and r later service positions in a uniform order → funding the first r positions, service the next r; reason: in a uniform order any two disjoint blocks of positions have the same joint law
--   - encoding: (7) with 2r ≤ T, r ≥ T/5 → 2r ≤ T ≤ 5r; reason: same condition over the integers
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.3, Lemma 2.4, p.6, eq. (7); proof, p.7

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_iidE
import Definitions.Def_AvgValueAlloc_OPTon
import Definitions.Def_AvgValueAlloc_OPToff
import Definitions.Def_AvgValueAlloc_posSet
import Definitions.Def_AvgValueAlloc_groupSum
import Definitions.Def_AvgValueAlloc_Hobj
import Definitions.Def_AvgValueAlloc_restrictTo
import Definitions.Def_AvgValueAlloc_HsL

namespace AvgValueAlloc

open scoped ENNReal

/-- **Lemma 2.4 (Benchmark capture), with (7) and the local capture of its proof.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.3, Lemma 2.4, p.6: "For r = ⌊T/3⌋ ≥ 1 funding and r later
service positions in a uniform T-item order, EH_G(M, Z) ≥ r² OPT_off(Q)/(4T(T − 1)) ≥
OPT_off(Q)/100. More generally, for i.i.d. funding and g(B) = E_{Z∼D^r}G_Z(B),
E max_X {W(X) + g(B(X))} ≥ OPT_on(D, T)/2280 (2r ≤ T, r ≥ T/5). (7)"; proof, p.7: "If every sponsor
is local, the independent shift keeps each anchor's whole comparison bundle with probability at
least 1/2. Writing H^s_L for the shifted objective restricted to retained local funding, the same
argument gives OPT_off(Q) ≤ 200EH^s_L(M, Z)." Setting: `H_G(M, Z) = max_X {W(X) + G_Z(B(X))}`,
p.6; the local schedule of §3, p.7.

For thresholds `ρ > 0`:
1. for a live sequence `Q` of `T` items with `r = ⌊T/3⌋ ≥ 1`, in uniform order with funding
   `M` the first `r` positions and service `Z` the next `r`:
   `E H_G(M, Z) ≥ r² OPT_off(Q)/(4T(T − 1)) ≥ OPT_off(Q)/100`;
2. for every finite law `D` and `r` with `2r ≤ T ≤ 5r`:
   `E_{M∼D^r} H_g(M) ≥ OPT_on(D, T)/2280` with `g(B) = E_{Z∼D^r} G_Z(B)`;
3. if every sponsor of `Q` is local and `r = ⌊T/3⌋ ≥ 1`, then with `K ∼ Bin(2r, 1/2)`,
   a fair shift `s ∈ {0,1}`, a uniform order, funding `M` the positions `K, …, K + r − 1` and
   service `Z` the next `2r − K` positions: `OPT_off(Q) ≤ 200 E H^s_L(M, Z)`.

**Formalization Note.** In a uniform order any two disjoint blocks of positions have the same joint
law, so fixing the funding block first and the service block next is the page's "r funding and r
later service positions". -/
theorem lemma_2_4 {n : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) :
    (∀ (T : ℕ) (Q : Fin T → Vec n), 1 ≤ T / 3 →
      ENNReal.ofReal (((T / 3 : ℕ) : ℝ) ^ 2 / (4 * (T : ℝ) * ((T : ℝ) - 1))) * OPToff ρ Q ≤
          ENNReal.ofReal ((∑ τ : Equiv.Perm (Fin T),
            Hobj ρ (Gdy ρ (seg Q τ (T / 3) (T / 3))) (seg Q τ 0 (T / 3))) / (T.factorial : ℝ)) ∧
        ENNReal.ofReal (1 / 100) * OPToff ρ Q ≤
          ENNReal.ofReal (((T / 3 : ℕ) : ℝ) ^ 2 / (4 * (T : ℝ) * ((T : ℝ) - 1))) * OPToff ρ Q) ∧
    (∀ (D : FinLaw n), D.IsLaw → ∀ T r : ℕ, 2 * r ≤ T → T ≤ 5 * r →
      OPTon ρ D T ≤ ENNReal.ofReal (2280 * iidR D (Fin r) fun M =>
        Hobj ρ (fun B => iidR D (Fin r) fun Z => Gdy ρ Z B) M)) ∧
    (∀ (T : ℕ) (Q : Fin T → Vec n), 1 ≤ T / 3 → AllSponsorsLocal ρ Q →
      OPToff ρ Q ≤ ENNReal.ofReal (200 *
        ∑ K ∈ Finset.range (2 * (T / 3) + 1), ∑ s ∈ Finset.range 2, ∑ τ : Equiv.Perm (Fin T),
          (((2 * (T / 3)).choose K : ℝ) / 2 ^ (2 * (T / 3))) * (1 / 2) * (1 / (T.factorial : ℝ)) *
            HsL ρ s (seg Q τ K (T / 3)) (seg Q τ (K + T / 3) (2 * (T / 3) - K)))) := by sorry

end AvgValueAlloc
