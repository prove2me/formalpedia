-- Prove2me | Theorems.Thm_Auto_triangularHilbert_integrand_comp
-- name    : Auto.triangularHilbert_integrand_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:03.766227+00:00
-- url     : https://prove2.me/theorems/b98fe51b-ac2b-4fa4-b448-169f647a287a
-- title:
--   Auto: triangular Hilbert integrand comp
-- statement:
--   The coordinate substitution identifies the two truncated integrands pointwise.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8330-L8351
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8330-L8351

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.triangularHilbert_integrand_comp (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ)
    (q : (ℝ × ℝ) × ℝ) :
    (let r := triangularSpaceEquiv q
     if ε < |r.1.1 + r.1.2 + r.2| then
       F₀ r.1 * F₁ (r.1.2, r.2) * F₂ (r.2, r.1.1) / ((r.1.1 + r.1.2 + r.2 : ℝ) : ℂ) else 0) =
    -(if ε < |q.2| then F₀ q.1 *
      triangularShiftProduct (triangularPullback₁ F₁) (triangularPullback₂ F₂) q.1 q.2 /
        (q.2 : ℂ) else 0) := by sorry
