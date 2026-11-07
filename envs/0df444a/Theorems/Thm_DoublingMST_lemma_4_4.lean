-- Prove2me | Theorems.Thm_DoublingMST_lemma_4_4
-- name    : DoublingMST.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:15.561198+00:00
-- url     : https://prove2.me/theorems/40a3d48c-4cb1-42e0-8832-84f2b9eb137a
-- title:
--   Lemma 4.4 — middle-level time complexity
-- statement:
--   There is an absolute constant $C>0$ with the following property. Assume $|X|=n\ge2$ and minimum interpoint distance $>1$, let $N$ be a net hierarchy, $t\ge32$, $\Gamma>1$, and let $\Psi$ be any output of Algorithm 1 on $N$ with parameter $t$. Then
--
--   $$\sum_{(u,v)\in\Psi}\min\{|B(u,2^{\operatorname{lev}(u)+2})|,\Gamma\}\cdot\min\{|B(v,2^{\operatorname{lev}(v)+2})|,\Gamma\}\le t^{C\operatorname{ddim}(X)}\,n\,\Gamma.$$
--
--   With $\Gamma=\gamma=\epsilon^{-1}\log(1/\epsilon)$ this bounds the total cost of the brute-force closest-pair searches at middle levels.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - encoding: the §2.1 standing assumption that the minimum interpoint distance of X is greater than 1 (p.12) → hypothesis MinDistGtOne d; reason: the source assumes it throughout §§2.1–4 (it is what makes level-0 balls singletons)
--   - reading: Ψ constructed from Lemma 3.3 with parameter t ≥ 32 → every output of Algorithm 1 on the hierarchy with parameter t ≥ 32; reason: Lemma 3.3's Ψ is Algorithm 1's output; the bound holds for every run
--   - reading: t^{O(ddim)} → ∃ C > 0, chosen before the space, t and Γ, with factor t^{C · ddim(X)}; reason: the standard meaning of the O
--   - generalization: §2.2 (p.13): "we can assume henceforth that the minimum interpoint distance of X is greater than 1 and the diameter of X is ∆ ≤ n^{10}/ϵ" → no upper bound on the diameter; minimum distance > 1 is kept; reason: the proof (pp.26–27) uses only Lemma 3.3 (5), (4) and |B(u, 4)| ≤ 2^{O(ddim)}, and the statement specializes to the source's by adding the bound
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 4.4, p.24 (PDF p.26); proof pp.26–27

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_MinDistGtOne
import Definitions.Def_DoublingMST_ddim
import Definitions.Def_DoublingMST_ball
import Definitions.Def_DoublingMST_IsAlg1Output
open scoped Classical

namespace DoublingMST

/-- **Lemma 4.4 (middle-level time complexity).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 4.4, p.24 (PDF p.26): "Let Γ > 1 and let Ψ be constructed from Lemma 3.3 with
parameter t ≥ 32. Then Σ_{(u,v)∈Ψ} min{|B(u, 2^{lev(u)+2})|, Γ} · min{|B(v, 2^{lev(v)+2})|, Γ} ≤
t^{O(ddim)} nΓ."

There is an absolute `C > 0` such that, under the standing assumptions of §2.1, for every net
hierarchy `H`, every `t ≥ 32`, every `Γ > 1` and **every** output `Ψ` of Algorithm 1 on `H` with
parameter `t`,
$$\sum_{(u,v)\in\Psi} \min\{|B(u, 2^{\mathrm{lev}(u)+2})|, \Gamma\} \cdot
  \min\{|B(v, 2^{\mathrm{lev}(v)+2})|, \Gamma\} \le t^{C\,\mathrm{ddim}(X)} \, n \, \Gamma.$$

**Formalization Note.** One `C` for every `t ≥ 32` and `Γ > 1`; `ddim` is that of `X`. -/
theorem lemma_4_4 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ d : Fin n → Fin n → ℝ, IsMetric d →
    MinDistGtOne d → ∀ (H : NetHierarchy d) (t Γ : ℝ), 32 ≤ t → 1 < Γ →
    ∀ Ψ : Finset ((Fin n × ℕ) × (Fin n × ℕ)), IsAlg1Output H t Ψ →
      ∑ uv ∈ Ψ, min ((ball d uv.1.1 ((2 : ℝ) ^ (uv.1.2 + 2))).card : ℝ) Γ *
          min ((ball d uv.2.1 ((2 : ℝ) ^ (uv.2.2 + 2))).card : ℝ) Γ ≤
        t ^ (C * ddim d) * n * Γ := by sorry

end DoublingMST
