-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_5_8
-- name    : DNFSatMQ.Main.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:33:32.905981+00:00
-- url     : https://prove2.me/theorems/fb180b5e-a406-4431-9efb-fba69a7227f3
-- title:
--   Lemma 5.8 — rejected free coordinates: Pr[L_{c⋆} ≥ u, H_k] ≤ √(|F|/|C⋆|) 2^{k−u/2}
-- statement:
--   **Setting (§5.1).** $f = \bigvee_{c'\in T} c'$ for a set $T$ of at most $s$ noncontradictory terms, $F = f^{-1}(1)$, and $c_\star \in T$ is fixed, with satisfying set $C_\star$. The scan starts at $x\sim U_{C_\star}$ and uses an independent uniform permutation $\pi \in S_n$; $z_0 = x, z_1,\dots,z_n$ are its states and $I$ its rejected coordinates. For $c' \in T$, $K_{c'} = \mathrm{Fix}(c')\cap\mathrm{Free}(c_\star)$; $H_k$ is the event that each visited point satisfies some $c'\in T$ with $|K_{c'}|\le k$; $E_{c_\star} = |\mathrm{Fix}(c_\star)\setminus I|$ and $L_{c_\star} = |I\cap\mathrm{Free}(c_\star)|$.
--
--   For every integer $k\ge 0$ and every $u\ge0$,
--   $$\Pr_{x,\pi}[L_{c_\star}\ge u,\ H_k] \le \sqrt{\frac{|F|}{|C_\star|}}\; 2^{k-u/2}.$$
--
--   Differences from the source:
--   - encoding: a term: literals on distinct variables → a partial assignment `Conj n = Fin n → Option Bool`; reason: §2 defines terms as noncontradictory; same objects
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - encoding: scan steps t = 1, …, n examine π(t) → steps t = 0, …, n−1 examine `π t`; `permRev π = π ∘ rev`; reason: 0-based indexing; same scan
--   - reading: every u ≥ 0 → every real u ≥ 0; reason: the source does not say whether u is an integer; the real reading contains the integer one
--   - encoding: §5 setup: T has at most s terms → T any finite set of terms (no bound s); reason: the bound does not involve s; every finite T has |T| ≤ s for s = |T|
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 5.8, p. 18 (PDF 19)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Scan

namespace DNFSatMQ.Main

/-- Lemma 5.8 (p. 18). -/
theorem lemma_5_8 {n : ℕ} (T : Finset (Conj n)) (cstar : Conj n) (hc : cstar ∈ T) (k : ℕ)
    (u : ℝ) (hu : 0 ≤ u) :
    prob (withPerm cstar.unif) {p | u ≤ (countL T cstar p.1 p.2 : ℝ) ∧ eventH T cstar k p.1 p.2} ≤
      Real.sqrt (((unionSet T).card : ℝ) / cstar.cube.card) * (2 : ℝ) ^ ((k : ℝ) - u / 2) := by sorry

end DNFSatMQ.Main
