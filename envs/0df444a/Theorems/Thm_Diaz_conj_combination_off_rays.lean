-- Prove2me | Theorems.Thm_Diaz_conj_combination_off_rays
-- name    : Diaz.conj_combination_off_rays
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T12:12:56.434017+00:00
-- url     : https://prove2.me/theorems/926f2540-2d5b-4750-893b-093edbd4d06a
-- title:
--   A rational combination $au+b\bar u$ lies off both rational rays
-- statement:
--   Let $u \in \mathbb{C}$ lie off the two axes, that is $\bar u \neq u$ and $\bar u \neq -u$ (equivalently $\operatorname{Im} u \neq 0$ and $\operatorname{Re} u \neq 0$), and let $a,b \in \mathbb{Q}^\times$. Then
--
--   $$\mu \;=\; au + b\bar u \;\notin\; \mathbb{Q}u \,\cup\, \mathbb{Q}\bar u .$$
--
--   In particular $\mu \neq 0$, which is the instance $c = 0$ of either clause.
--
--   **Where this sits.** This is the closing clause of Carlo Perassi's mixed-coordinate rigidity theorem at a Diaz point. The theorem takes $u$ on the Diaz locus, puts $\rho = u\bar u$, and for $\mu \in \mathcal{L} \setminus (\mathbb{Q}u \cup \mathbb{Q}\bar u)$ concludes
--
--   $$\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}\bigl(u,\mu,e^{\rho/\mu}\bigr) \;\ge\; 2 .$$
--
--   Its final paragraph verifies that the headline instance $\mu = au + b\bar u$ with $a,b \in \mathbb{Q}^\times$ really does satisfy that hypothesis: a relation $au + b\bar u \in \mathbb{Q}u \cup \mathbb{Q}\bar u$ would force $\bar u/u \in \mathbb{Q}$ and put $u$ on the axes. This node is exactly that verification, and it is **unconditional** — the deep input of that theorem is Théorème 7.1 of Roy–Waldschmidt (1997), which is not available in this Mathlib revision and is not on the mission graph.
--
--   **Proof.** Off the axes, $u$ and $\bar u$ are linearly independent over $\mathbb{Q}$ (`Diaz.indep_of_not_axis`: from $\operatorname{Re} u \neq 0$ and $\operatorname{Im} u \neq 0$, a relation $xu + y\bar u = 0$ with $x,y \in \mathbb{Q}$ gives $x + y = 0$ on real parts and $x - y = 0$ on imaginary parts, hence $x = y = 0$).
--
--   * If $au + b\bar u = cu$ with $c \in \mathbb{Q}$, then $(a-c)u + b\bar u = 0$, so $b = 0$ — contradicting $b \neq 0$.
--   * If $au + b\bar u = c\bar u$ with $c \in \mathbb{Q}$, then $au + (b-c)\bar u = 0$, so $a = 0$ — contradicting $a \neq 0$.
--
--   **Formalisation notes.** The hypothesis is stated in the off-axes form $\overline u \neq u \wedge \overline u \neq -u$, which is the weakest form and is exactly what `Diaz.indep_of_not_axis` consumes; a consumer working on the Diaz locus obtains it from `Diaz.not_on_axes`. The two ray exclusions quantify over all $c \in \mathbb{Q}$ (not merely $\mathbb{Q}^\times$), so the non-vanishing $\mu \neq 0$ that the theorem notes separately is the case $c = 0$ and is not stated as a third conjunct.
--
--   **Source.** Carlo Perassi, unpublished apart from this node: the closing paragraph of the proof of his mixed-coordinate rigidity theorem. The mathematics is his; this node records one step of it in Lean and claims no novelty of its own. Elementary.
-- source:
--   Carlo Perassi, unpublished apart from this node: the closing paragraph of the proof of his mixed-coordinate rigidity theorem at a Diaz point.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.conj_combination_off_rays {u : ℂ}
    (h1 : conj u ≠ u) (h2 : conj u ≠ -u)
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ c : ℚ, (a : ℂ) * u + (b : ℂ) * conj u ≠ (c : ℂ) * u) ∧
      (∀ c : ℚ, (a : ℂ) * u + (b : ℂ) * conj u ≠ (c : ℂ) * conj u) := by sorry
