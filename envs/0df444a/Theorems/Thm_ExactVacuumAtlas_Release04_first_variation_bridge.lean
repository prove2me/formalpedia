-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release04_first_variation_bridge
-- name    : ExactVacuumAtlas.Release04.first_variation_bridge
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:48.148975+00:00
-- url     : https://prove2.me/theorems/9c3aa426-b240-4b77-9572-5ac3217c0e92
-- title:
--   Off-shell first-variation bridge for the Einstein–Maxwell residual (goal)
-- statement:
--   Off-shell first-variation bridge for the Einstein–Maxwell residual (goal)
--
--   Let (g_ε, ginv_ε, F_ε), ε ∈ ℝ, be four-dimensional component fields on an open set W ⊆ ℝ × ℝ⁴ satisfying FamilyData, and let (h, f) be the genuine ε-derivative of (g_ε, F_ε) at ε = 0 on the slice {y : (0, y) ∈ W} (IsTangent). Then for every x with (0, x) ∈ W and all indices: d/dε|₀ E_ab(g_ε, ginv_ε, F_ε)(x) = LE_ab(g_0, ginv_0, F_0; h, f)(x), d/dε|₀ J^b(g_ε, ginv_ε, F_ε)(x) = LJ^b(g_0, ginv_0, F_0; h, f)(x), and d/dε|₀ H_abc(F_ε)(x) = LH_abc(f)(x), each as a Mathlib HasDerivAt at ε = 0. Residuals (registered H1–H8, 4D): E_ab = R_ab − ½ g_ab R − 2 S_ab with R = Σ g^{ab} R_ab and S_ab = Σ_{c,d} F_ac g^{cd} F_bd − ¼ g_ab F_cd F^{cd} (F^{ab} = Σ g^{ac} g^{bd} F_cd, raised with the given ginv); J^b = Σ_a (∂_a F^{ab} + Σ_k (Γ^a_{ak} F^{kb} + Γ^b_{ak} F^{ak})) (an upper-index vector); H_abc = ∂_a F_bc + ∂_b F_ca + ∂_c F_ab (a covariant 3-index quantity). E is a covariant 2-index quantity. Linearised residuals (registered J1–J10) are specified independently by finite sums and coordinate derivatives; they are not defined as the parameter derivative of the nonlinear residual. In particular, with K = invVar ginv h = −G h G (G = ginv) and C = chrVar g ginv h, LE_ab = δR_ab − ½ (h_ab R + g_ab δR) − 2 δS_ab, LJ^b = Σ_a [∂_a V^{ab} + Σ_k (C^a_{ak} F^{kb} + Γ^a_{ak} V^{kb} + C^b_{ak} F^{ak} + Γ^b_{ak} V^{ak})] with V = raise2Var, LH_abc = ∂_a f_bc + ∂_b f_ca + ∂_c f_ab.
--
--   **Scope.** FamilyData contains exactly: W open; (ε, y) ↦ g_ε,ij(y) and (ε, y) ↦ F_ε,ij(y) are C^∞ on W; ginv_ε(y) · g_ε(y) = 1 (true left inverse, as 4×4 matrices) at every (ε, y) ∈ W. It does NOT assume symmetry of g, a Lorentzian signature, antisymmetry of F or any field equation; it is a derivative contract for the finite coordinate expressions, not a statement that an arbitrary matrix field is a physical metric. Physical backgrounds enter only through the full EinsteinMaxwellCertificate. The statement is off-shell: no residual is assumed to vanish, and no family of solutions is assumed.
--
--   **中文摘要** 离壳一阶变分桥：对满足 FamilyData 的同一四维族、同一切向 (h,f) 与基点 (0,x)∈W，E、J、H 三个残差在 ε=0 的真实导数分别等于显式算子 LE、LJ、LH。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/Release04/Main.lean#L18-L30; SHA-256 94d44d182696e6c3af85a2817fd1482158d86225c075ab29a5234cea70217e62. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_Transport_MatrixCalc
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.Variation

theorem ExactVacuumAtlas.Release04.first_variation_bridge {g ginv : ℝ → Metric 4} {F : ℝ → TwoForm 4} {W : Set (ℝ × Pt 4)}
    {h : Metric 4} {f : TwoForm 4} (hfam : FamilyData g ginv F W) (ht : IsTangent g F W h f)
    {x : Pt 4} (hx : ((0 : ℝ), x) ∈ W) :
    (∀ a b : Fin 4, HasDerivAt (fun ε => einsteinMaxwell (g ε) (ginv ε) (F ε) a b x)
      (linEinstein (g 0) (ginv 0) (F 0) h f a b x) 0) ∧
    (∀ b : Fin 4, HasDerivAt (fun ε => maxwellDiv (g ε) (ginv ε) (F ε) b x)
      (linMaxwell (g 0) (ginv 0) (F 0) h f b x) 0) ∧
    (∀ a b c : Fin 4, HasDerivAt (fun ε => faradayCyclic (F ε) a b c x) (linFaraday f a b c x) 0) := by sorry
