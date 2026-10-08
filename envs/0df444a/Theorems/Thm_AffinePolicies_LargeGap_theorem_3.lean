-- Prove2me | Theorems.Thm_AffinePolicies_LargeGap_theorem_3
-- name    : AffinePolicies.LargeGap.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:09:47.841253+00:00
-- url     : https://prove2.me/theorems/5aaa8fc0-da1c-4c39-95e8-adff1bafb5ad
-- title:
--   Theorem 3, PDF p. 16 — on the instance ℐ of (19), z_Aff(𝒰) > (m^{1/2−δ}/4) · z_Adapt(𝒰)
-- statement:
--   Let $\delta>0$ and let $m$ be a positive integer with $m^\delta>200$ (condition (18)). Consider the two-stage adaptive problem $\Pi_{\mathrm{Adapt}}(\mathcal U)$ on the instance $\mathcal I$ of (19): $n_1=n_2=m$, $c=0$, $d=(1,\dots,1)^\top$, $A=0$, $B_{ii}=1$ and $B_{ij}=\theta_0=m^{-(1-\delta)/2}$ for $i\ne j$, and
--   $$\mathcal U=\operatorname{conv}\bigl\{0,\ e_1,\dots,e_m,\ \tfrac{1}{\sqrt m}e,\ \theta_0\mathbf 1_S\ (|S|=\lceil m^{1-\delta}\rceil)\bigr\}.$$
--   Then the worst-case cost of an optimal affine policy exceeds the fully-adaptable optimum by a factor of order $m^{1/2-\delta}$:
--   $$z_{\mathrm{Aff}}(\mathcal U)>\frac{m^{1/2-\delta}}{4}\cdot z_{\mathrm{Adapt}}(\mathcal U).$$
--
--   The paper states this as $z_{\mathrm{Aff}}(\mathcal U)=\Omega(m^{1/2-\delta})\cdot z_{\mathrm{Adapt}}(\mathcal U)$ for any given $\delta>0$; the constant $1/4$ is the one its proof establishes (the contradiction hypothesis (27) is $z_{\mathrm{Aff}}(\mathcal U)\le m^{1/2-\delta}/4$, and Lemma 4 gives $z_{\mathrm{Adapt}}(\mathcal U)\le1$). Since affine policies are within $O(\sqrt m)$ of the optimum on every instance of this class (Theorem 4), the example shows that this bound is tight up to the factor $m^{\delta}$.
--
--   **Formalization Note** $z_{\mathrm{Aff}}$ and $z_{\mathrm{Adapt}}$ are infima of the worst-case costs achieved by feasible (affine, respectively arbitrary) policies, with affine policies required to be nonnegative on $\mathcal U$. Powers are real powers. The explicit form with constant $1/4$ is stronger than the asymptotic statement on the page.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 3, PDF p. 16 (proof PDF p. 22–25)

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

namespace AffinePolicies.LargeGap

theorem theorem_3 (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) :
    (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 * AffinePolicies.Simplex.zAdapt (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) <
      AffinePolicies.Simplex.zAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) := by sorry

end AffinePolicies.LargeGap
