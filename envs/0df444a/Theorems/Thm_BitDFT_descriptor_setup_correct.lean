-- Prove2me | Theorems.Thm_BitDFT_descriptor_setup_correct
-- name    : BitDFT.descriptor_setup_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:04:01.10199+00:00
-- url     : https://prove2.me/theorems/17469ae1-c939-4c26-b096-1ff550be3f74
-- title:
--   Prepare two counted-block descriptor tapes in exactly word length plus three steps
-- statement:
--   For every binary descriptor y and arbitrary parked native tape, the descriptor-setup machine reaches its specified final configuration in exactly |y|+3 transitions. The count includes moving the target heads off their markers, writing leading separators, copying each bit to both targets, and writing trailing separators while placing the target heads at the low-order end. Empty descriptors and leading zeros are supported. Routing the source and allocating the blank target tapes are explicit prerequisites.
-- source:
--   Descriptor initialization for the previously proved counted-block machine in the finite-precision DFT transfer.

import Definitions.Def_BitDFT_DescriptorSetup
open BitDFT.DescriptorSetup IntMul

theorem BitDFT.descriptor_setup_correct (base : machine.Cfg) (y : List Bool) :
    machine.step^[y.length+3] (initial base y) = final base y := by sorry
