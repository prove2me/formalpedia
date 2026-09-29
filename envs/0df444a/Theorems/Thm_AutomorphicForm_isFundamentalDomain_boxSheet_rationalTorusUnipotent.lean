-- Prove2me | Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
-- name    : AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/92d56380-2026-5b80-9154-fa368dc88d98
-- title:
--   Box sheet is a fundamental domain for B(K)
-- statement:
--   Let $K$ be a number field, with the adele ring $\mathbb{A}_K$ and $\mathrm{GL}_2(\mathbb{A}_K)$ carrying their Borel measurable structures. Put $B$ for the image, under the map $\mathrm{GL}_2(K)\to\mathrm{GL}_2(\mathbb{A}_K)$ induced by $K\to\mathbb{A}_K$ (`globalPoints`), of the subgroup `borelSubgroup K` of those matrices whose $(1,0)$ entry vanishes; put $H :=$ `rationalTorusUnipotent K`, the subgroup $(\text{rationalCentre}\sqcup\text{rationalDiagOne})\sqcup N(\mathbb{A}_K)$ of $\mathrm{GL}_2(\mathbb{A}_K)$, where $N(\mathbb{A}_K)$ is the range of $u\mapsto n(u)$ on $\mathbb{A}_K$; and put $T\subseteq H$ for the image of `adelicBox K` $=\{x : x_\infty\in\text{infiniteBox }K,\ x_{\mathrm f}\in\widehat{\mathcal O}_K\}$ under $u\mapsto n(u)$, viewed in $H$. The measure on $H$ is `rationalTorusUnipotentHaar K`, the sum over $(z,a)\in K^\times\times K^\times$ of the translates by $z\cdot I\cdot\mathrm{diagOne}(a)$ of the pushforward along $u\mapsto n(u)$ of $\mu(\text{adelicBox }K)^{-1}\mu$, with $\mu$ the additive Haar measure on $\mathbb{A}_K$. The theorem asserts: $B\le H$; $B$ is countable; $T$ is measurable; $T$ is a fundamental domain for the action of $B$, regarded as a subgroup of $H$, on $H$ with respect to that measure; and for every measurable $F\colon H\to[0,\infty]$, $\int_T F\,d(\text{rationalTorusUnipotentHaar }K)=\int_{\text{adelicBox }K}F(n(u))\,d\big(\mu(\text{adelicBox }K)^{-1}\mu\big)(u)$.
--
--   This is the unfolding step of the Rankin–Selberg method on $\mathrm{GL}_2$ which replaces an integral over $B(K)\backslash H$ by an integral over $N(K)\backslash N(\mathbb{A}_K)\cong K\backslash\mathbb{A}_K$, realised concretely by the box sheet $\{n(u):u\in\text{adelicBox }K\}$, normalised so that the total mass is one. It is used in the estimates for pseudo-Eisenstein series and in the comparison of truncated integrals over Siegel sets with Iwasawa-coordinate integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent.lean

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent
    (K : Type) [Field K] [NumberField K] :
    let B : Subgroup (AdelicGL2 (𝓞 K) K) := (borelSubgroup K).map (globalPoints (𝓞 K) K)
    let T : Set (rationalTorusUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    B ≤ rationalTorusUnipotent K ∧ Countable B ∧ MeasurableSet T ∧
    IsFundamentalDomain (B.subgroupOf (rationalTorusUnipotent K)) T (rationalTorusUnipotentHaar K) ∧
    ∀ F : rationalTorusUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalTorusUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by sorry
